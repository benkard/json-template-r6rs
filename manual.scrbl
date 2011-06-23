#lang scribble/manual
@(require scribble/eval)
@(require racket/sandbox)
@(require (for-label r6rs))
@;@(require (for-label "json-template.s6l"))
@(require "json-template.s6l")

@;@defmodule/this-package[json-template]

@(define r6rs-evaluator
   (call-with-trusted-sandbox-configuration
    (lambda ()
      (parameterize ([sandbox-output 'string]
                     [sandbox-error-output 'string])
        (make-evaluator
         'r6rs
         '(import (rnrs) (json-template)))))))
@(define racket-evaluator
   (call-with-trusted-sandbox-configuration
    (lambda ()
      (parameterize ([sandbox-output 'string]
                     [sandbox-error-output 'string])
        (make-evaluator
         'racket/base
         #:requires (list 'json-template))))))


@title{JSON Template for R6RS}
@author{Matthias A. Benkard}


@section{Installation}

@subsection{Installing pregexp}

Download the pregexp library from @url{http://evalwhen.com/pregexp/}.  Wrap @filepath{pregexp.scm} in the following form (replacing ``....'' with the file's original content):

@schemeblock[
(library (pregexp)
  (export pregexp
          pregexp-match
          pregexp-match-positions
          pregexp-split
          pregexp-replace
          pregexp-replace*
          pregexp-quote)
  (import (rnrs) (rnrs mutable-pairs))
  
  ....

)
]

You can then install @filepath{pregexp.scm} as an R6RS library.  For details on how to do this, consult the manual of your Scheme implementation.

As an example, @codeblock[@"plt-r6rs --install pregexp.scm"] will work on @hyperlink["http://racket-lang.org/"]{Racket}.


@subsection{Installing JSON Template for R6RS}

JSON Template for R6RS is provided as a ready-to-use R6RS library file.  Simply install @filepath{json-template.s6l} as per the manual of the Scheme implementation of your choice.

On Racket, @codeblock[@"plt-r6rs --install json-template.s6l"] ought to work just fine.


@section{Usage}

@subsection{API}

@defproc[(make-template [template-data string?]) procedure?]{
  Create a template from @scheme[template-data], which must be in JSON Template syntax.

  The returned procedure expects a single argument, the @italic{subtitution context}, and returns the expanded template as a string.  Three types of contexts are supported:

  @itemlist[
    @item{@bold{Primitive contexts.}  These may be of any form whatever (valid primitive contexts are lists, numbers, symbols, strings, etc.) and are not treated specially.  Their only purpose is being printed into the template expansion as plain text.  Note that a primitive context does not make a whole lot of sense when used as an argument to @scheme{make-template} (although it can be used as such and referenced as @scheme["@"]); it is much more commonly encountered as a nested context in a map.}
    @item{@bold{Sequences.}  At present, these may only be lists.  They can be iterated over by the use of repeated sections.}
    @item{@bold{Maps.}  These may be either hash tables or association lists.  They can be indexed into by substitutions.}
  ]
  
  @scheme[make-template]'s behavior can be customized by the parameters @scheme[formatters], @scheme[meta-left], @scheme[meta-right], @scheme[default-formatter], and @scheme[format-char].

  For general information about JSON Template, see @url{http://json-template.googlecode.com/svn/trunk/doc/Introducing-JSON-Template.html} and @url{http://code.google.com/p/json-template/wiki/Reference}.
}


@subsection{Examples}

@interaction[#:eval r6rs-evaluator
(define template (make-template "
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
"))
(template '((title . "<Registered People>")
            (people .
                    (((name . "Nathalie") (age . 24))
                     ((name . "Heinrich") (age . 28))
                     ((name . "Hans")     (age . 25))))))
(template '((title . "<Registered People>")
            (people)))
(template '((title . "<Registered People>")))
]
