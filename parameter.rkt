#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide reduction-out
         current-language
         define-extended-reduction-relation
         define-reduction-relation
         define-extended-metafunction
         define-extended-judgment)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require (for-syntax racket/base
                     racket/list
                     racket/sequence
                     racket/provide-transform
                     syntax/parse
                     syntax/id-set
                     syntax/id-table
                     (only-in redex/private/term-fn
                              judgment-form-mode))
         (only-in redex/private/struct empty-reduction-relation)
         (only-in redex/private/judgment-form
                  judgment-form-id?
                  lookup-judgment-form-id)
         (only-in redex/private/term
                  term-fn-id?)
         racket/stxparam
         redex/reduction-semantics)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relation transformer

(begin-for-syntax
  ;; Reduction relation transformer struct. Contains the transformer itself
  ;; as well as a field containing the parameters.
  (struct reduction-relation-transformer (parameters defaults roots transformer)
    #:property prop:procedure 3)

  ;; Returns the parameters of a reduction relation transformer.
  (define (get-params rr)
    (reduction-relation-transformer-parameters (syntax-local-value rr)))

    ;; Returns the defaults of a reduction relation transformer.
  (define (get-defaults rr)
    (reduction-relation-transformer-defaults (syntax-local-value rr)))

  ;; Returns the defaults of a reduction relation transformer.
  (define (get-roots rr)
    (reduction-relation-transformer-roots (syntax-local-value rr)))
  )

(define-syntax empty-rr
  (reduction-relation-transformer '() '() '() (λ _ #'empty-reduction-relation)))

(define-syntax reduction-out
  (make-provide-transformer
   (λ (stx modes)
     (syntax-parse stx
       [(_ ?r:id)
        #:with (?param ...) (get-params #'?r)
        (expand-export
         #'(combine-out ?r ?param ...)
         '())]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Binding syntax class

(begin-for-syntax
  ;; Syntax class for binding set when applying a reduction relation for
  ;; parameterization. The bindings returned are what are used for the syntax
  ;; parameterization.
  (define-splicing-syntax-class (bindings params)
    ;; Explicit parameterization
    (pattern
     (~seq [x y] ...)
     #:fail-when
     (check-duplicate-identifier (syntax->list #'(x ...)))
     "duplicate parameter"
     #:fail-when
     (check-valid-parameter params #'(x ...))
     "invalid parameter"))

  ;; If we attempt to parameterize a reduction relation, make sure that it's
  ;; valid (i.e. we originally defined the relation with those parameters).
  (define (check-valid-parameter params xs)
    (define param-set
      (immutable-free-id-set params))
    (for/first ([x (in-syntax xs)]
                #:when (not (free-id-set-member? param-set x)))
      x))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Defining extensions

(begin-for-syntax
  (define extension-table (make-free-id-table))

  (define (record-extension! base lang name)
    (when (identifier? base)
      (define lang-table
        (free-id-table-ref! extension-table base make-free-id-table))
      (free-id-table-set! lang-table lang name)))

  (define (lookup-extension base lang)
    (define lang-table
      (free-id-table-ref extension-table base (λ () #f)))
    (and lang-table (free-id-table-ref lang-table lang (λ () #f))))

  (define-syntax-class metafunction
    (pattern (_ base:id lang:id name:id : rest ...))
    (pattern (_ base:id lang:id [(name:id _ ...) _ ...] _ ...)))
  )

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lifts

(begin-for-syntax
  (define (lift-metafunction var default root lang)
    (define extension (lookup-extension root lang))
    (define name (datum->syntax #f (gensym)))
    (cond
      [extension (list #'(void) var extension extension)]
      [else
       (list
        #`(define-metafunction/extension
            #,default
            #,lang
            #,name : any (... ...) -> any)
        var
        name
        root)]))

  (define (lift-judgment var default root lang)
    (define extension (lookup-extension root lang))
    (define name (datum->syntax #f (gensym)))
    (define mode
      (judgment-form-mode (lookup-judgment-form-id default)))
    (cond
      [extension (list #'(void) var extension extension)]
      [else
       (list
        #`(define-extended-judgment-form
            #,lang
            #,default
            #:mode (#,name #,@mode))
        var
        name
        root)]))

  (define (lift-reduction-relation var default root lang)
    (define extension (lookup-extension root lang))
    (define name (datum->syntax #f (gensym)))
    (cond
      [extension (list #'(void) var extension extension)]
      [else
       (list
        #`(-define-extended-reduction-relation
            #,name
            #,default
            #,lang)
        var
        name
        root)]))

  (define (lift-generic var default root lang)
    (cond
      [(judgment-form-id? default) (lift-judgment var default root lang)]
      [(term-fn-id? default) (lift-metafunction var default root lang)]
      [(maybe-reduction-relation? default)
       (lift-reduction-relation var default root lang)]))

  (define (lift-parameters lang base new-vars new-defaults)
    (define base-lifts
      (cond
        [(parameterized-reduction-relation? base)
         (define base-vars (get-params base))
         (define base-defaults (get-defaults base))
         (define base-roots (get-roots base))
         (for/list ([var (in-list base-vars)]
                    [default (in-list base-defaults)]
                    [root (in-list base-roots)])
           (lift-generic var default root lang))]
        [else '()]))
    (define new-lifts
      (for/list ([var (in-syntax new-vars)]
                 [default (in-syntax new-defaults)])
        (lift-generic var default default lang)
        #;(list #'(void) var default default)))
    (append base-lifts new-lifts))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relation transformer constructor

(define-rename-transformer-parameter current-language
  (make-rename-transformer #'current-language-error))

(define-syntax (current-language-error stx)
  (raise-syntax-error
   #f
   "cannot use current-language outside of parameterized reduction relation"
   stx))

(begin-for-syntax
  (define (make-reduction-relation-transformer
           base lang -params -defaults -roots rests)
    (define params (syntax->list -params))
    (define defaults (syntax->list -defaults))
    (define roots (syntax->list -roots))
    (reduction-relation-transformer
     params
     defaults
     roots
     (syntax-parser
       ;; Lifts
       [?r:id
        #:with (?x ...) params
        #:with (?y ...) defaults
        #`(syntax-parameterize ([current-language
                                 (make-rename-transformer #'#,lang)]
                                [?x (make-rename-transformer #'?y)] ...)
            (?r #:disable))]

       ;; No parameterization
       [(?r:id #:disable)
        (if (parameterized-reduction-relation? base)
            #`(extend-reduction-relation (#,base #:disable) #,lang #,@rests)
            #`(extend-reduction-relation #,base #,lang #,@rests))]

       ;; Explicit parameterization
       [(?r:id ?bs)
        #:declare ?bs (bindings params)
        #:with (?x ...) params
        #:with (?y ...) defaults
        #`(syntax-parameterize ([current-language
                                 (make-rename-transformer #'#,lang)]
                                [?x (make-rename-transformer #'?y)] ...)
            (syntax-parameterize ([?bs.x (make-rename-transformer #'?bs.y)] ...)
              (?r #:disable)))])))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relations as parameters

(begin-for-syntax
  (define (parameterized-reduction-relation? stx)
    (and (identifier? stx)
         (let ([stx-val (syntax-local-value stx (λ () #f))])
           (reduction-relation-transformer? stx-val))))

  (define (maybe-reduction-relation? stx)
    (define not-bound-id?
      (or (not (identifier? stx))
          (not (syntax-local-value stx (λ () #f)))))
    (or not-bound-id? (parameterized-reduction-relation? stx)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relation

(define-syntax (-define-extended-reduction-relation stx)
  (syntax-parse stx
    [(_ ?name:id
        ?base
        ?lang:id
        (~optional (~seq #:parameters ([?var:id ?default:id] ...))
                   #:defaults ([(?var 1) '()] [(?default 1) '()]))
        ?rest ...)
     #:with ([?defn ?var* ?default* ?root*] ...)
     (lift-parameters #'?lang #'?base #'(?var ...) #'(?default ...))
     #'(begin
         (define-rename-transformer-parameter ?var
           (make-rename-transformer #'?default)) ...
         ?defn ...
         (define-syntax ?name
           (make-reduction-relation-transformer
            #'?base #'?lang
            #'(?var* ...) #'(?default* ...) #'(?root* ...)
            #'((... ...) (?rest ...)))))]))

(define-syntax (define-extended-reduction-relation stx)
  (syntax-parse stx
    [(_ ?name:id ?base ?lang:id ?rest ...)
     #'(begin
         (-define-extended-reduction-relation ?name ?base ?lang ?rest ...)
         (begin-for-syntax
           (record-extension! #'?base #'?lang #'?name)))]))

(define-syntax (define-reduction-relation stx)
  (syntax-parse stx
    [(_ ?name:id
        ?lang:id
        ?rest ...)
     #'(define-extended-reduction-relation ?name
         empty-rr ?lang
         ?rest ...)]))
