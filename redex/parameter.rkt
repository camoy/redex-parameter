#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide define-extended-reduction-relation
         define-reduction-relation
         define-extended-metafunction
         define-extended-judgment)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex/reduction-semantics
         (only-in redex/private/struct empty-reduction-relation)
         (only-in redex/private/judgment-form
                  judgment-form-id?
                  lookup-judgment-form-id)
         (for-syntax racket/base
                     racket/sequence
                     racket/syntax
                     racket/function
                     racket/list
                     racket/match
                     syntax/parse
                     syntax/id-set
                     syntax/id-table
                     syntax/strip-context
                     (only-in redex/private/term-fn
                              judgment-form-mode)))


(begin-for-syntax
  (require debug-scopes)
  (define (p stx)
    (displayln (+scopes stx))
    stx))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relation transformer

(begin-for-syntax
  ;; Reduction relation transformer struct. Contains the transformer itself
  ;; as well as a field containing the parameters.
  (struct rr-transformer (parameters transformer) #:property prop:procedure 1)

  ;; Returns the parameters of a reduction relation transformer.
  (define (get-params rr)
    (rr-transformer-parameters (syntax-local-value rr)))

  ;; A parameter scope allows us to shadow existing uses of metafunctions and
  ;; judgments in a definition. When we add the scope, uses are redirecetd to the
  ;; syntax parameter instead of the original definition.
  (define param-scope
    (make-syntax-introducer))

  ;; Adds given scope to all elements in a syntax list
  (define (add-scope-to-all introducer stxs)
    (for/list ([stx (in-syntax stxs)])
      (introducer stx 'add)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parameter extensions

(begin-for-syntax
  (define extension-table (make-free-id-table))

  (define (record-extension! base lang name)
    (define lang-table
      (free-id-table-ref! extension-table base make-free-id-table))
    (free-id-table-set! lang-table lang name))

  (define (lookup-extension base lang)
    (define lang-table
      (free-id-table-ref extension-table base (λ () #f)))
    (and lang-table (free-id-table-ref lang-table lang (λ () #f))))

  (define (extended-params base lang)
    (define params (get-params base))
    (map syntax-local-introduce
         (filter-map (λ (param)
                       (lookup-extension param lang))
                     params)))

  (define (inherited-params base lang explicit-params)
    (define explicit-set
      (immutable-free-id-set (syntax->list explicit-params)))
    (define params (get-params base))
    (map syntax-local-introduce
         (filter (λ (param)
                   (and (not (lookup-extension param lang))
                        (not (free-id-set-member? explicit-set param))))
                 params)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lifts

(begin-for-syntax
  ;; Mutable table that maps language identifiers to a scope that is used to
  ;; distinguish multiple definitions of a base metafunction or judgment.
  (define language-scopes
    (make-free-id-table))

  ;; Given a language and a piece of syntax, attach an existing language scope
  ;; if it exists, or create a new language scope.
  (define (add-language-scope lang stx)
    (define introducer
      (free-id-table-ref! language-scopes lang make-syntax-introducer))
    (introducer stx 'add))

  (define-syntax-class metafunction
    (pattern (_ base:id lang:id name:id : rest ...))
    (pattern (_ base:id lang:id [(name:id _ ...) _ ...] _ ...)))

  (define (lift-metafunction mf lang)
    (define mf* (add-language-scope lang mf))
    #`(define-metafunction/extension
        #,mf
        #,lang
        #,mf* : any (... ...) -> any))

  (define (lift-judgment jf lang)
    (define jf* (add-language-scope lang jf))
    (define mode
      (judgment-form-mode (lookup-judgment-form-id jf)))
    #`(define-extended-judgment-form
        #,lang
        #,jf
        #:mode (#,jf* #,@mode)))

  (define (lift-parameters lang params)
    (for/list ([param (in-syntax params)])
      (cond
        [(judgment-form-id? param) (lift-judgment param lang)]
        [else (lift-metafunction param lang)])))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Binding syntax class

(begin-for-syntax
  ;; Syntax class for binding set when applying a reduction relation for
  ;; parameterization. The bindings returned are what are used for the syntax
  ;; parameterization.
  (define-splicing-syntax-class (bindings base lang params rr-bindings base-bindings)
    ;; Explicit parameterization
    (pattern
     (~seq [x y] ...)
     #:fail-when
     (check-duplicate-identifier (syntax->list #'(x ...)))
     "duplicate parameter"
     #:fail-when
     (check-valid-parameter params #'(x ...))
     "invalid parameter"))


  (define (would-bind? x y)
    (bound-identifier=?
     y
     ((make-syntax-delta-introducer y x) x)))

  (define (bound-by-one-of? x ys)
    (for/or ([y (in-syntax ys)])
      (would-bind? y x)))

  ;; If we attempt to parameterize a reduction relation, make sure that it's
  ;; valid (i.e. we originally defined the relation with those parameters).
  (define (check-valid-parameter params xs)
    (for/first ([x (in-syntax xs)]
                #:when (not (bound-by-one-of? x params)))
      x))

  ;; Adds the appropriate scopes to the parameters.
  (define (pre-process-params params lang)
    (for/list ([x (in-syntax params)])
      (define y-extended (lookup-extension x lang))
      (define y-lifted (add-language-scope lang x))
      (list x (or y-extended y-lifted))))

    ;; Adds the appropriate scopes to the parameters.
  (define (pre-process-base-params base lang explicit-params)
    (define explicit-params-list (syntax->list explicit-params))
    (define explicit-table
      (make-immutable-free-id-table
       (map cons explicit-params-list explicit-params-list)))
    (define params (get-params base))
    (for/list ([x (in-syntax params)])
      (define y-explicit (free-id-table-ref explicit-table x (λ () #f)))
      (define y-extended (lookup-extension x lang))
      (define y-lifted (add-language-scope lang x))
      (list x (or y-explicit y-extended y-lifted))))

  ;; Adds the appropriate scopes to the parameters.
  (define (process-params bindings lang xs ys)
    (define explicit-table
      (make-free-id-table (map cons (syntax->list xs) (syntax->list ys))))
    (for/list ([binding (in-syntax bindings)])
      (match-define (list x y) (syntax->list binding))
      (define y-explicit
        (or (free-id-table-ref explicit-table x (λ () #f))
            (free-id-table-ref explicit-table y (λ () #f))))
      (list x (param-scope x 'add) (or y-explicit y))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relation transformer

(begin-for-syntax
  (define (make-rr-transformer name base lang more params rr-bindings base-bindings)
    (rr-transformer
     (syntax->list params)
     (syntax-parser
       [x:id #`(x)]
       [(_ ?bs)
        #:declare ?bs (bindings base lang params rr-bindings base-bindings)
        #:with ([_ ?x ?y] ...)
        (process-params rr-bindings lang #'(?bs.x ...) #'(?bs.y ...))
        #:with ([?bx _ ?by] ...)
        (process-params base-bindings lang #'(?bs.x ...) #'(?bs.y ...))
        #`(let-syntax
              ([?x (make-rename-transformer #'?y)]
               ...)
            #,@(lift-parameters lang params)
            (extend-reduction-relation
             (#,base [?bx ?by] ...)
             #,lang
             #,@(add-scope-to-all param-scope more)))])))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relation

;; Returns syntax that defines a base reduction relation.
(define-syntax (define-extended-reduction-relation stx)
  (syntax-parse stx
    [(_ ?name:id ?base:id ?lang:id
        #:parameters (?explicit-param:id ...) ?more ...)
     #:with (?extended-param ...) (extended-params #'?base #'?lang)
     #:with (?inherited-param ...)
     (inherited-params #'?base #'?lang #'(?explicit-param ...))
     #:with (?new-param ...) #'(?extended-param ... ?explicit-param ...)
     #:with (?param ...) #'(?new-param ... ?inherited-param ...)
     #:with (?rr-binding ...) (pre-process-params #'(?param ...) #'?lang)
     #:with (?base-binding ...)
     (pre-process-base-params #'?base #'?lang #'(?explicit-param ...))
     #`(begin
         (define-syntax ?name
           (make-rr-transformer
            #'?name #'?base #'?lang
            #'((... ...) (?more ...))
            #'(?param ...)
            #'(?rr-binding ...)
            #'(?base-binding ...))))]
    [(_ ?name:id ?base:id ?lang:id ?more ...)
     #'(define-extended-reduction-relation
         ?name ?base ?lang #:parameters ()
         ?more ...)]))

(define-syntax (define-reduction-relation stx)
  (syntax-parse stx
    [(_ ?name:id ?lang:id #:parameters (?new-param:id ...) ?more ...)
     #:with ?base (gensym)
     #'(begin
         (define-syntax ?base
           (rr-transformer (list) (λ _ #'empty-reduction-relation)))
         (define-extended-reduction-relation ?name ?base ?lang
           #:parameters (?new-param ...) ?more ...))]
    [(_ ?name:id ?lang:id ?more ...)
     #'(define-reduction-relation ?name ?lang #:parameters () ?more ...)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Defining extensions

(define-syntax (define-extended-metafunction stx)
  (syntax-parse stx
    [(~and ?mf:metafunction (_ ?all ...))
     #'(begin
         (define-metafunction/extension ?all ...)
         (begin-for-syntax
           (record-extension! #'?mf.base #'?mf.lang #'?mf.name)))]))

(define-syntax (define-extended-judgment stx)
  (syntax-parse stx
    [(_ ?base:id ?lang:id #:mode (?name:id ?modes ...) ?more ...)
     #'(begin
         (define-extended-judgment-form ?lang ?base
           #:mode (?name ?modes ...)
           ?more ...)
         (begin-for-syntax
           (record-extension! #'?base #'?lang #'?name)))]))
