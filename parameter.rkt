#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide reduction-out
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
  (struct reduction-relation-transformer (parameters defaults transformer)
    #:property prop:procedure 2)

  ;; Returns the parameters of a reduction relation transformer.
  (define (get-params rr)
    (reduction-relation-transformer-parameters (syntax-local-value rr)))

    ;; Returns the defaults of a reduction relation transformer.
  (define (get-defaults rr)
    (reduction-relation-transformer-defaults (syntax-local-value rr)))
  )

(define-syntax empty-rr
  (reduction-relation-transformer '() '() (λ _ #'empty-reduction-relation)))

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
  (define (lift-metafunction var default lang)
    (define extension (lookup-extension default lang))
    (define name (datum->syntax #f (gensym)))
    (cond
      [extension (list #'(void) var extension)]
      [else
       (list
        #`(define-metafunction/extension
            #,default
            #,lang
            #,name : any (... ...) -> any)
        var
        name)]))

  (define (lift-judgment var default lang)
    (define extension (lookup-extension default lang))
    (define name (datum->syntax #f (gensym)))
    (define mode
      (judgment-form-mode (lookup-judgment-form-id default)))
    (cond
      [extension (list #'(void) var extension)]
      [else
       (list
        #`(define-extended-judgment-form
            #,lang
            #,default
            #:mode (#,name #,@mode))
        var
        name)]))

  (define (lift-reduction-relation var default lang)
    (define extension (lookup-extension default lang))
    (define name (datum->syntax #f (gensym)))
    (cond
      [extension (list #'(void) var extension)]
      [else
       (list
        #`(define-extended-reduction-relation
            #,name
            #,default
            #,lang)
        var
        name)]))

  (define (lift-parameters lang base new-vars new-defaults)
    (define base-lifts
      (cond
        [(parameterized-reduction-relation? base)
         (define base-vars (get-params base))
         (define base-defaults (get-defaults base))
         (for/list ([var (in-list base-vars)]
                    [default (in-list base-defaults)])
           (cond
             [(judgment-form-id? default) (lift-judgment var default lang)]
             [(term-fn-id? default) (lift-metafunction var default lang)]
             [(maybe-reduction-relation? default)
              (lift-reduction-relation var default lang)]))]
        [else '()]))
    (define new-lifts
      (for/list ([var (in-syntax new-vars)]
                 [default (in-syntax new-defaults)])
        (list #'(void) var default)))
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
           base lang -params -defaults rests)
    (define params (syntax->list -params))
    (define defaults (syntax->list -defaults))
    (reduction-relation-transformer
     params
     defaults
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

(define-syntax (define-extended-reduction-relation stx)
  (syntax-parse stx
    [(_ ?name:id
        ?base
        ?lang:id
        (~optional (~seq #:parameters ([?var:id ?default:id] ...))
                   #:defaults ([(?var 1) '()] [(?default 1) '()]))
        ?rest ...)
     #:with ([?defn ?var* ?default*] ...)
     (lift-parameters #'?lang #'?base #'(?var ...) #'(?default ...))
     #'(begin
         (define-rename-transformer-parameter ?var
           (make-rename-transformer #'?default)) ...
         ?defn ...
         (define-syntax ?name
           (make-reduction-relation-transformer
            #'?base #'?lang
            #'(?var* ...) #'(?default* ...)
            #'((... ...) (?rest ...))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require (for-syntax racket/base)
           redex/reduction-semantics
           rackunit
           syntax/macro-testing
           racket/set)

  (define (apply-rr . xs)
    (apply set (apply apply-reduction-relation xs)))

  ;; L0

  (define-language L0
    [m ::= number]
    [E ::= (wrap E) hole])

  (define-metafunction L0
    [(-foo-mf m) 1])

  (define-judgment-form L0
    #:mode (-foo-jf I O)
    [(-foo-jf m 1)])

  (define-reduction-relation r0-mf
    L0
    #:parameters ([foo-mf -foo-mf])
    [--> m (foo-mf m)])

  (define-reduction-relation r0-jf
    L0
    #:parameters ([foo-jf -foo-jf])
    [--> m_1 m_2 (judgment-holds (foo-jf m_1 m_2))])

  (define-reduction-relation r0-rr
    L0
    #:parameters ([r r0-mf])
    [--> m_1 m_2
         (where (_ ... m_2 _ ...)
                ,(apply-reduction-relation r (term m_1)))])

  (test-case "Normal functioning."
    (check-equal? (apply-rr r0-mf (term 0)) (set 1))
    (check-equal? (apply-rr r0-jf (term 0)) (set 1))
    (check-equal? (apply-rr r0-rr (term 0)) (set 1)))

  (define-metafunction L0
    [(-bar-mf m) 2])

  (define-judgment-form L0
    #:mode (-bar-jf I O)
    [(-bar-jf m 2)])

  (define r* (r0-mf [foo-mf -bar-mf]))

  (test-case "Explicit parameterization."
    (check-equal? (apply-rr (r0-mf [foo-mf -bar-mf]) (term 0)) (set 2))
    (check-equal? (apply-rr (r0-jf [foo-jf -bar-jf]) (term 0)) (set 2))
    (check-equal? (apply-rr (r0-rr [r r*]) (term 0)) (set 2)))

  (test-case "Explicit parameterization failures."
    (check-exn
     #rx"invalid parameter"
     (λ () (convert-syntax-error (apply-rr (r0-mf [oops-mf bar-mf]) (term 0)))))

    (check-exn
     #rx"duplicate parameter"
     (λ ()
       (convert-syntax-error (apply-rr (r0-mf [foo-mf -bar-mf]
                                              [foo-mf -bar-mf])
                                       (term 0))))))

  ;; L1

  (define-extended-language L1 L0
    [m ::= .... string])

  (define normal-rr
    (reduction-relation
     L0
     [--> m 1]))

  (define-extended-reduction-relation normal-extended
    normal-rr L1
    [--> m 10])

  (test-case "Extension of normal reduction relation."
    (check-equal? (apply-rr normal-extended (term "hi")) (set 1 10)))

  (define-extended-reduction-relation r1-rr-no-extend r0-rr L1)

  (test-case "Implicit lifting of reduction relation."
    (check-equal? (apply-rr r1-rr-no-extend (term "hi")) (set 1)))

  (define-extended-reduction-relation r1-mf
    r0-mf L1
    [--> m 13])

  (define-extended-reduction-relation r1-jf
    r0-jf L1
    [--> m 13])

  (define-extended-reduction-relation r1-rr r0-rr L1)

  (test-case "Normal extension."
    (check-equal? (apply-rr r1-mf (term 0)) (set 1 13))
    (check-equal? (apply-rr r1-jf (term 0)) (set 1 13)))

  (test-case "Extension with implicit lifting."
    (check-equal? (apply-rr r1-mf (term "hi")) (set 1 13))
    (check-equal? (apply-rr r1-jf (term "hi")) (set 1 13))
    (check-equal? (apply-rr r1-rr (term "hi")) (set 1 13)))

  (test-case "Explicit parameterization of an extension."
    (check-equal? (apply-rr (r1-mf [foo-mf -bar-mf]) (term 0)) (set 2 13))
    (check-equal? (apply-rr (r1-jf [foo-jf -bar-jf]) (term 0)) (set 2 13)))

  (define-metafunction L1
    [(-foo-mf* m) 3])

  (define-judgment-form L1
    #:mode (-foo-jf* I O)
    [(-foo-jf* m 3)])

  (define-extended-reduction-relation r1-mf*
    r0-mf L1 #:parameters ([foo-mf* -foo-mf*])
    [--> m (foo-mf* m)])

  (define-extended-reduction-relation r1-jf*
    r0-jf L1 #:parameters ([foo-jf* -foo-jf*])
    [--> m_1 m_2 (judgment-holds (foo-jf* m_1 m_2))])

  (test-case "Normal extension with new parameter."
    (check-equal? (apply-rr r1-mf* (term 0)) (set 1 3))
    (check-equal? (apply-rr r1-jf* (term 0)) (set 1 3)))

  (test-case "Explicit parameterization of an new parameter."
    (check-equal? (apply-rr (r1-mf* [foo-mf* -bar-mf]) (term 0)) (set 1 2))
    (check-equal? (apply-rr (r1-jf* [foo-jf* -bar-jf]) (term 0)) (set 1 2))
    (check-equal? (apply-rr (r1-mf* [foo-mf -bar-mf] [foo-mf* -bar-mf]) (term 0))
                  (set 2))
    (check-equal? (apply-rr (r1-jf* [foo-jf -bar-jf] [foo-jf* -bar-jf]) (term 0))
                  (set 2)))

  (define-extended-metafunction -foo-mf L1
    [(-foo-mf** m) 4])

  (define-extended-judgment -foo-jf L1
    #:mode (-foo-jf** I O)
    [(-foo-jf** m 4)])

  (define-extended-reduction-relation r1-mf** r0-mf L1)
  (define-extended-reduction-relation r1-jf** r0-jf L1)

  (test-case "Normal extension with parameter from extension."
    (check-equal? (apply-rr r1-mf** (term 0)) (set 4))
    (check-equal? (apply-rr r1-jf** (term 0)) (set 1 4)))

  (define-extended-reduction-relation r0-mf-wrap
    (context-closure s current-language E)
    L0
    #:parameters ([s r0-mf]))

  (test-case "Extend closure of reduction relation."
    (check-equal? (apply-rr r0-mf-wrap (term (wrap 0)))
                  (set (term (wrap 1)))))

  (define-extended-reduction-relation r1-mf-wrap r0-mf-wrap L1)

  (test-case "Closure with reduction relation extension."
    (check-equal? (apply-rr r1-mf-wrap (term (wrap "hi")))
                  (set (term (wrap 4)))))
  )
