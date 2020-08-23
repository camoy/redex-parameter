#lang scribble/manual

@require[@for-label["../parameter.rkt"
                    redex/reduction-semantics
                    racket/base]
         racket/sandbox
         scribble/example]

@(define evaluator
  (make-base-eval
    '(require redex/reduction-semantics
              redex/parameter)))

@title{Redex Parameters}
@author{Cameron Moy}

@defmodule[redex/parameter]

This package implements forms for
parameterized Redex objects
(i.e. metafunctions, judgment forms,
and reduction relations).
When objects depend
on one another,
for example
a reduction relation
is defined using a metafunction,
parameters can automatically
lift dependencies from
the lower language
to a higher one.

@section{Examples}

Suppose we define a language @racket[L0],
a metafunction @racket[L0-number-bad],
and a reduction relation @racket[r0-bad].
We will rely on this metafunction,
defined for @racket[L0],
in our reduction relation.

@examples[#:eval evaluator #:no-result
  (define-language L0
    [m ::= number])

  (define-metafunction L0
    L0-number-bad : m -> m
    [(L0-number-bad m) 0])

  (define-reduction-relation r0-bad
    L0
    [--> m (L0-number-bad m)])]

As expected, we can see what happens when we
step with @racket[r0-bad].

@examples[#:eval evaluator #:label #f
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

@examples[#:eval evaluator #:no-result
  (define-extended-language L1 L0
    [m ::= .... string])

  (define-extended-reduction-relation r1-bad r0-bad L1)]

Here we've added to the @racket[m] non-terminal.
Since @racket[r1-bad] extends @racket[r0-bad],
every rule will be reinterpreted.
The only case we have will match,
but the metafunction @racket[L0-number-bad]
is undefined for strings.
This will yield an error.

@examples[#:eval evaluator #:label #f
  (eval:error (apply-reduction-relation r1-bad "hi"))]

This package solve the problem
by introducing parameters.
We'll instead define @racket[r0] with
@racket[define-reduction-relation*]
and parameterize it by the metafunction
defined with
@racket[define-metafunction*].

@examples[#:eval evaluator #:no-result
  (define-metafunction* L0
    L0-number : m -> m
    [(L0-number m) 0])

  (define-reduction-relation* r0
    L0
    #:parameters ([lang-number L0-number])
    [--> m (lang-number m)])]

We'ved replace the non-starred variants from earlier,
with their starred counterparts.
Using the starred form gets you two things:
@itemlist[
@item{
@italic{Liftable}.
You can use the object as the value of a parameter.
}
@item{
@italic{Parameters}.
You can introduce parameters that will lift their values appropriately.
}]

Here we introduce a parameter @racket[lang-number]
that is bound to @racket[L0-number].
For @racket[L0] there is no difference between
@racket[r0] and @racket[r0-bad].

@examples[#:eval evaluator #:label #f
  (apply-reduction-relation r0 999)]

However if we do the extension as before,
the parameter's default value will be
lifted to the current language.

@examples[#:eval evaluator #:label #f
  (define-extended-reduction-relation* r1 r0 L1)
  (apply-reduction-relation r1 "hi")]

Now suppose instead of giving back a
language level of @racket[0],
we'd like it to give back @racket[1].
One way to do this is to extend
the original metafunction.

@examples[#:eval evaluator #:label #f
  (define-extended-metafunction* L0-number L1
    L1-number : m -> m
    [(L1-number m) 1])
  (define-extended-reduction-relation* r1* r0 L1)
  (apply-reduction-relation r1* "hi")]

As we just saw,
if no metafunction extends the original parameter value,
in our case @racket[L0-number],
then it is lifted.
However,
if a metafunction does extend it,
in this case @racket[L1-number],
that will be used instead.

Parameters are not limited to
just reduction relations.
You can,
for example,
parameterize a judgment form by a metafunction
or parameterize a metafunction by a reduction relation.

@section{Reference}

@defform[(redex-out id ...)]{
  Exports the given parameterized objects.
  Without this,
  the provided objects will not be recognized as liftable.
}

@defform[(define-reduction-relation* id
           language parameters
           domain codomain base-arrow
           reduction-case ...
           shortcuts)
           #:grammar
           [(parameters (code:line)
                        (code:line #:parameters ([parameter default] ...)))]]{
  Defines @racket[id]
  as a parameterized reduction relation.
  Aside from parameters,
  the syntax is the same as in @racket[reduction-relation].
}

@defform[(define-extended-reduction-relation* id
           reduction-relation language parameters
           domain codomain base-arrow
           reduction-case ...
           shortcuts)
           #:grammar
           [(parameters (code:line)
                        (code:line #:parameters ([parameter default] ...)))]]{
  Defines @racket[id]
  as a parameterized reduction relation
  that extends an existing one.
  Aside from parameters,
  the syntax is the same as in @racket[extend-reduction-relation].
}

@defform[(define-metafunction* language
           parameters
           metafunction-contract
           metafunction-case ...)
         #:grammar
         [(parameters (code:line)
                      (code:line #:parameters ([parameter default] ...)))]]{
  Defines a parameterized metafunction.
  Aside from parameters,
  the syntax is the same as in @racket[define-metafunction].
  Parameterized metafunctions must have a contract.
}

@defform[(define-extended-metafunction* metafunction-id language
           parameters
           metafunction-contract
           metafunction-case ...)
         #:grammar
         [(parameters (code:line)
                      (code:line #:parameters ([parameter default] ...)))]]{
  Defines a parameterized metafunction
  that extends @racket[metafunction-id].
  Aside from parameters,
  the syntax is the same as in @racket[define-metafunction/extension].
  Parameterized metafunctions must have a contract.
}

@defform[(define-judgment-form* language
           parameters
           mode-spec
           contract-spec
           invariant-spec
           rule ...)
         #:grammar
         [(parameters (code:line)
                      (code:line #:parameters ([parameter default] ...)))]]{
  Defines a parameterized judgment form.
  Aside from parameters,
  the syntax is the same as in @racket[define-judgment-form].
  Parameterized judgments may not be modeless.
}

@defform[(define-extended-judgment* judgment-id language
           parameters
           mode-spec
           contract-spec
           invariant-spec
           rule ...)
         #:grammar
         [(parameters (code:line)
                      (code:line #:parameters ([parameter default] ...)))]]{
  Defines a parameterized judgment form
  that extends @racket[judgment-id].
  Aside from parameters,
  the syntax is the same as in @racket[define-extended-judgment-form].
  Parameterized judgments may not be modeless.
}

@deftogether[(@defform[(define-reduction-relation id
                         language
                         domain codomain base-arrow
                         reduction-case ...
                         shortcuts)]
              @defform[(define-extended-reduction-relation id
                         reduction-relation language
                         domain codomain base-arrow
                         reduction-case ...
                         shortcuts)]
              @defform[(define-extended-metafunction metafunction-id language
                         metafunction-contract
                         metafunction-case ...)])]{
  These are non-parameterized variants of the above
  starred variants;
  they are provided only for consistency.
}
