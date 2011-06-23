#!r6rs
;;; -*- mode: scheme; coding: utf-8 -*-
;;; Copyright 2011, Matthias Andreas Benkard.

(library (json-template)
 (export make-template
         formatters
         meta-left
         meta-right
         default-formatter
         format-char)
 (import (rnrs base) (rnrs programs) (rnrs unicode) (rnrs lists) (rnrs control)
         (rnrs records syntactic) (rnrs records procedural) (rnrs records inspection)
         (rnrs exceptions) (rnrs conditions) (rnrs io simple) (rnrs io ports) (rnrs hashtables)
         (rnrs r5rs) (srfi :39) (srfi :28)
         ;; Racket-specific:
         (only (racket)
               regexp-quote regexp-replace regexp regexp-split regexp-match)
         (only (racket mpair)
               list->mlist)
         
         )
 
 ;; Racket-specific:
 (define pregexp-quote regexp-quote)
 (define pregexp-split (lambda args (list->mlist (apply regexp-split args))))
 (define pregexp regexp)
 (define pregexp-replace regexp-replace)
 (define pregexp-match
   (lambda args
     (let ([m (apply regexp-match args)])
       (and m
            (list->mlist m)))))
 
(define meta-left (make-parameter "{"))
(define meta-right (make-parameter "}"))
(define default-formatter (make-parameter "raw"))
(define format-char (make-parameter "|"))

(define-syntax λ
  (syntax-rules ()
    [(_ forms ...)
     (lambda forms ...)]))

(define (dict? x)
  (or (list? x)
      (hashtable? x)))

(define (dict-ref dict key default)
  (let* ([default-default (cons #f #f)]
         [result
          (cond
            [(list? dict)
             (let ([result-cons (assoc key dict)])
               (if result-cons
                   (cdr result-cons)
                   default-default))]
            [(hashtable? dict)
             (hashtable-ref dict key default-default)])])
    (if (eq? result default-default)
        (if (procedure? default)
            (default)
            default)
        result)))

(define (template-string->chunks input meta-left meta-right)
  (let* ([meta-left-re   (pregexp-quote meta-left)]
         [meta-right-re  (pregexp-quote meta-right)]
         [re (regexp
              (string-append "(" meta-left-re ")|(" meta-right-re ")"))])
    (pregexp-split re input)))

(define (flip-flop-map f1 f2 lst)
  "Like map, but alternate between f1 and f2 as the function to apply."
  (letrec ((flip (λ (items)
                   (cond
                     [(null? items)'()]
                     [else         (cons (f1 (car items)) (flop (cdr items)))])))
           (flop (λ (items)
                   (cond
                     [(null? items)'()]
                     [else         (cons (f2 (car items)) (flip (cdr items)))]))))
    (flip lst)))

(define (classify-chunks chunks format-char)
  (flip-flop-map (λ (x) x)
                 (λ (x) (parse-directive x format-char))
                 chunks))

(define (parse-directive directive format-char)
  (cond
    [(pregexp-match "^#" directive)
     #f]
    [(pregexp-match "^\\.section[ \t]+(.*)$" directive)
     => (λ (x) (list 'section (cadr x)))]
    [(pregexp-match "^\\.repeated[ \t]+section[ \t]+(.*)$" directive)
     => (λ (x) (list 'repeated-section (cadr x)))]
    [(string=? ".end" directive)
     (list 'end)]
    [(string=? ".or" directive)
     (list 'or)]
    [(pregexp-match "^\\.alternates\\s+with$" directive)
     (list 'alternates-with)]
    [else
     (cons 'substitute (pregexp-split (pregexp-quote format-char)
                                            directive))]))
  
(define (remove-spurious-newlines-from-token-groups groups)
  (let ([last-was-directive? #f])
    (map
      (λ (group)
        (if last-was-directive?
            (begin
              (set! last-was-directive? (pair? group))
              (if (string? group)
                  (pregexp-replace "^\n" group "")
                  group))
            (begin
              (set! last-was-directive? (pair? group))
              group)))
      groups)))

(define-record-type section
  (fields (immutable name)
          (immutable body)
          (immutable alternative)))

(define-record-type repeated-section
  (parent section)
  (fields (immutable alternates-with)))

(define-record-type substitution
  (fields (immutable name)
          (immutable formatter)
          (immutable arguments)))

(define (parse-structure parsed-groups)
  (let loop ([parsed-groups parsed-groups]
             [clauses '()])
    (if (or (null? parsed-groups)
            (and (pair? (car parsed-groups))
                 (memq (caar parsed-groups) '(end or alternates-with))))
        (values (reverse clauses)
                (and (pair? parsed-groups) (caar parsed-groups))
                (if (pair? parsed-groups) (cdr parsed-groups) '()))
        (let ([grp (car parsed-groups)])
          (cond
            [(string? grp)
             (loop (cdr parsed-groups)
                   (cons grp clauses))]
            [(eq? (car grp) 'section)
             (let-values ([(stuff reason rest)
                           (parse-structure (cdr parsed-groups))])
               (case reason
                 [(or)
                  (let-values ([(stuff2 _ rest2)
                                (parse-structure rest)])
                    (loop rest2 (cons (make-section (cadr grp) stuff stuff2) clauses)))]
                 [(end)
                  (loop rest (cons (make-section (cadr grp) stuff #f) clauses))]))]
          [(eq? (car grp) 'repeated-section)
           (let inner-loop ([subsections '()]
                            [rest (cdr parsed-groups)])
             (let-values ([(stuff reason new-rest)
                           (parse-structure rest)])
               (when (not reason)
                 (error "Premature end of file."))
               (if (eq? reason 'end)
                   (let inner-inner-loop
                       ([subsections (cons (cons 'end stuff) subsections)]
                        [alternative #f]
                        [alternates-with #f])
                     (if (null? (cdr subsections))
                         (loop new-rest
                               (cons (make-repeated-section (cadr grp)
                                                            (cdar subsections)
                                                            alternative
                                                            alternates-with)
                                     clauses))
                         (case (caadr subsections)
                           [(alternates-with)
                            (inner-inner-loop (cdr subsections)
                                              alternative
                                              (cdar subsections))]
                           [(or)
                            (inner-inner-loop (cdr subsections)
                                              (cdar subsections)
                                              alternates-with)]
                           [else
                            (error "Oh no, I don't know what I'm doing here!  Subsections:" subsections)])))
                   (inner-loop (cons (cons reason stuff) subsections) new-rest))))]
          [(eq? (car grp) 'substitute)
           (loop (cdr parsed-groups)
                 (if (null? (cddr grp))
                     (cons (make-substitution (cadr grp) #f '()) clauses)
                     (cons (make-substitution (cadr grp) (caddr grp) (cdddr grp)) clauses)))])))))

(define (parse-structure* x)
  (let-values ([(stuff reason rest) (parse-structure x)])
    stuff))

(define (make-template template-string)
  (let ([template-data
         (parse-structure*
          (remove-spurious-newlines-from-token-groups
           (classify-chunks (template-string->chunks template-string
                                                     (meta-left) (meta-right))
                            (format-char))))])
    (let ([default-formatter (default-formatter)])
      (λ (context)
        (expand-template template-data (list context) default-formatter)))))

(define (name->path name)
  (if (string=? name "@")
      '()
      (pregexp-split "\\." name)))

(define (resolve-path stack path)
  (if (null? stack)
      #f
      (let-values ([(value success?)
                    (resolve-path-in-object (car stack) path)])
        (if success?
            value
            (resolve-path (cdr stack) path)))))

(define (resolve-path-in-object context path)
  (let ([nothing (cons #f #f)])
    (cond [(null? path)
           (values context #t)]
          [(dict? context)
           (let ([y (dict-ref context
                              (car path)
                              (λ ()
                                (dict-ref context
                                          (string->symbol (car path))
                                          nothing)))])
             (if (eq? y nothing)
                 (values #f #f)
                 (resolve-path-in-object y (cdr path))))]
          [else
           (values #f #f)])))

(define (find-formatter name)
  (cdr (assoc name (formatters))))

(define (expand-template template stack default-formatter)
  (for-each
   (λ (thing)
    (cond
      [(repeated-section? thing)
       (let ([context (resolve-path stack (name->path (section-name thing)))])
         (if (or (not context)
                 (null? context))
             (when (section-alternative thing)
               (expand-template (section-alternative thing)
                                (cons context stack)
                                default-formatter))
             (let ([first-iteration? #t])
               (for-each
                (λ (value)
                 (when (repeated-section-alternates-with thing)
                   (if first-iteration?
                       (set! first-iteration? #f)
                       (expand-template (repeated-section-alternates-with thing)
                                        stack
                                        default-formatter)))
                 (expand-template (section-body thing)
                                  (cons value stack)
                                  default-formatter))
                context))))]
      [(section? thing)
       (let ([context (resolve-path stack (name->path (section-name thing)))])
         (if context
             (expand-template (section-body thing)
                              (cons context stack)
                              default-formatter)
             (when (section-alternative thing)
               (expand-template (section-alternative thing)
                                (cons context stack)
                                default-formatter))))]
      [(substitution? thing)
       (display ((find-formatter (or (substitution-formatter thing) default-formatter))
                 (resolve-path stack (name->path (substitution-name thing)))))]
      [else
       (display thing)]))
   template))

(define (make-escaper replacements)
  (let* ([escapees  (map car replacements)]
         [escapings (map cdr replacements)]
         [re        (regexp
                     (string-append "^(.*?)"
                                    "(?:("
                                    (fold-left (λ (acc x)
                                                 (string-append acc
                                                                ")|("
                                                                (pregexp-quote (string x))))
                                               (pregexp-quote (string (car escapees)))
                                               (cdr escapees))
                                    "))"
                                    "|$"))])
    (λ (thing)
        (call-with-string-output-port
         (λ (out)
           (let ([in (open-string-input-port (if (string? thing)
                                                 thing
                                                 (format "~a" thing)))])
             (let loop ()
               (if (eof-object? (peek-char in))
                   (values)
                   (let* ([m               (pregexp-match re in)]
                          [raw-text        (and m (cadr m))]
                          [escapee-matches (and m (cddr m))])
                     (when raw-text
                       (display raw-text out))
                     (for-each (λ (x y)
                                 (when x
                                   (display y out)))
                               escapee-matches
                               escapings)
                     (loop))))))))))


(define (escape-for-uri thing)
  (call-with-string-output-port
    (λ (out)
      (for-each
       (λ (char)
        (let ((cnum (char->integer char)))
          (if (or (<= (char->integer #\A) cnum (char->integer #\Z))
                  (<= (char->integer #\a) cnum (char->integer #\z))
                  (<= (char->integer #\0) cnum (char->integer #\9))
                  (member char
                          '(#\$ #\- #\_ #\. #\+ #\! #\* #\( #\) #\')))
              (display char out)
              ;; FIXME: This assumes that (< cnum 256).
              ;; Maybe we should interpret the data as a byte string
              ;; rather than as a string.  W3C says we ought to use
              ;; UTF-8 encoding, which is consistent with the Racket
              ;; default encoding:
              ;;
              ;;  http://www.w3.org/International/O-URL-code.html
              (if (< cnum 16)
                  (display (format "%0~x" cnum) out)
                  (display (format "%~x"  cnum) out)))))
        (if (string? thing)
            thing
            (format "~a" thing))))))


(define formatters
  (make-parameter
   `(("html"            . ,(make-escaper '((#\< . "&#60;")
                                           (#\> . "&#62;")
                                           (#\& . "&#38;"))))
     ("html-attr-value" . ,(make-escaper '((#\< . "&#60;")
                                           (#\> . "&#62;")
                                           (#\& . "&#38;")
                                           (#\' . "&#39;")
                                           (#\" . "&#34;"))))
     ("url-param-value" . ,escape-for-uri)
     ("raw"             . ,(λ (x) x)))))


#;
(let ([template (make-template "
<h1>{title|html}</h1>
{.section people}
<ul>
{.repeated section @}
  <li>{name} ({age} years)</li>
{.end}
</ul>
{.or}
<p>No one's registered.</p>
{.end}
")])
  (template '((title . "<Registered People>")
              (people .
                      (((name . "Nathalie") (age . 24))
                       ((name . "Heinrich") (age . 28))
                       ((name . "Hans")     (age . 25)))))))
)
