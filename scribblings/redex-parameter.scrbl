#lang scribble/manual
@require[@for-label["../parameter.rkt"
                    redex/reduction-semantics
                    racket/base]
         racket/sandbox
         scribble/example]

@(define redex-evaluator
   (parameterize ([sandbox-output 'string]
                  [sandbox-error-output 'string]
                  [sandbox-memory-limit 50])
     (make-evaluator 'racket/base
       #:requires '(redex/reduction-semantics
                    redex/parameter))))

@title{Redex Parameters}
@author{Cameron Moy}

@defmodule[redex/parameter]

This package implements forms for
parameterized reduction relations.
When extending reduction relations
that depend on metafunctions,
judgment forms,
or other reduction relations,
parameterized reduction relations
can automatically lift forms at
lower language levels.

@section{Examples}

Suppose we define a language @racket[L0],
a metafunction @racket[L0-number],
and a reduction relation @racket[r0-bad].
We will rely on this metafunction,
defined on @racket[L0],
in our reduction relation.

@examples[#:eval redex-evaluator #:no-result
  (define-language L0
    [m ::= number])

  (define-metafunction L0
    [(L0-number m) 0])

  (define r0-bad
    (reduction-relation
      L0
      [--> m (L0-number m)]))]

As expected, we can see what happens when we
step with @racket[r0-bad].

@examples[#:eval redex-evaluator #:label #f
  (apply-reduction-relation r0-bad 999)]

Why is @racket[r0-bad] named as such?
We've defined a reduction relation that
depends on a language-specific metafunction.
Unfortunately,
extended reduction relations will break
under these conditions.
An extended reduction relation will lift
all rules to the new language,
but metafunction and judgment form
dependencies will not be reinterpreted.

@examples[#:eval redex-evaluator #:no-result
  (define-extended-language L1 L0
    [m ::= .... string])

  (define r1-bad
    (extend-reduction-relation r0-bad L1))]

Here we've added a new form to the @racket[m]
non-terminal.
Since @racket[r1-bad] extends @racket[r0-bad],
every rule will be reinterpreted.
The only case we have will match,
but the metafunction @racket[L0-number]
is undefined for strings.
This will yield an error.

@examples[#:eval redex-evaluator #:label #f
  (eval:error (apply-reduction-relation r1-bad "hi"))]

Parameterized reduction relations solve this problem.
We'll instead define @racket[r0] with
@racket[define-reduction-relation]
and parameterize it by the metafunction.

@examples[#:eval redex-evaluator #:no-result
  (define-reduction-relation r0
    L0
    #:parameters ([lang-number L0-number])
    [--> m (lang-number m)])]

Here we introduce a parameter @racket[lang-number]
that by default is bound to @racket[L0-number]
as before.
For @racket[L0] there is no difference between
@racket[r0] and @racket[r0-bad].

@examples[#:eval redex-evaluator #:label #f
  (apply-reduction-relation r0 999)]

However if we do the extension as before,
the parameter's default value will be
lifted to the current language.

@examples[#:eval redex-evaluator #:label #f
  (define-extended-reduction-relation r1 r0 L1)
  (apply-reduction-relation r1 "hi")]

Now suppose instead of giving back a
language level of @racket[0],
we'd like it to give back @racket[1].
One way to do this is to extend
the original metafunction.

@examples[#:eval redex-evaluator #:label #f
  (define-extended-metafunction L0-number L1
    [(L1-number m) 1])
  (define-extended-reduction-relation r1* r0 L1)
  (apply-reduction-relation r1* "hi")]

As we just saw,
if no metafunction extends the original parameter value,
in our case @racket[L0-number],
then it is lifted.
However,
if a metafunction does extend it,
in this case @racket[L1-number],
that will be used instead.

If you want to set a parameter to a specific value,
you can give an explicit parameterization.

@examples[#:eval redex-evaluator #:label #f
  (define-metafunction L1
    [(silly m) "☺"])
  (apply-reduction-relation (r1 [lang-number silly]) "hi")]

As a special case,
you can provide @racket[#:disable]
to the parameterization and it will
disable all the automatic lifting and we get back
the original bad reduction relation's behavior.

@examples[#:eval redex-evaluator #:label #f
  (eval:error (apply-reduction-relation (r1 #:disable) "hi"))]

@section{Reference}

@defform[(define-reduction-relation id
           language parameters
           domain codomain base-arrow
           reduction-case ...
           shortcuts)
           #:grammar
           [(parameters (code:line)
                        (code:line #:parameters ([parameter default] ...)))]]{
  Defines @racket[id] as a parameterized reduction relation.
  Each @racket[parameter] is initially assigned to the @racket[default] value.
  The remaining arguments are as in @racket[reduction-relation].
}

@defform[(define-extended-reduction-relation id
           reduction-relation language parameters
           domain codomain base-arrow
           reduction-case ...
           shortcuts)
           #:grammar
           [(parameters (code:line)
                        (code:line #:parameters ([parameter default] ...)))]]{
  Defines @racket[id] as a parameterized reduction relation which extends
  an existing one.
  The set of parameters is extended with any new parameters.
  The remaining arguments are as in @racket[extend-reduction-relation].
}

@defform[(define-extended-metafunction metafunction-id language
           metafunction-contract
           metafunction-case ...)]{
  Defines a metafunction that extends @racket[metafunction-id].
  If @racket[metafunction-id] serves as the default value for a parameter,
  then the defined metafunction will serve as the default value of the parameter
  for @racket[language].
}

@defform[(define-extended-judgment judgment-id language
           mode-spec
           contract-spec
           invariant-spec
           rule ...)]{
  Defines a judgment form that extends @racket[judgment-id].
  If @racket[judgment-id] serves as the default value for a parameter,
  then the defined judgment form will serve as the default value of the parameter
  for @racket[language].
}

@defform[(reduction-out id)]{
Exports the parameterized reduction relation @racket[id]
and its parameters.
}
