#lang racket/base

(require (for-syntax racket/base
                     racket/hash
                     racket/match
                     racket/set
                     racket/sequence
                     racket/pretty
                     debug-scopes
                     syntax/strip-context
                     syntax/parse
                     syntax/id-table
                     syntax/id-set)
         racket/splicing
         redex/reduction-semantics)

(begin-for-syntax
  (define-splicing-syntax-class params
    (pattern (~seq #:parameters ([param:id val:id] ...)))
    (pattern (~seq)
             #:attr (param 1) null
             #:attr (val 1) null))

  ;;

  (struct extensible (params vals maker) #:transparent)
  (define extension-table (make-free-id-table))
  (define extension-table-next #f)

  (define (add-extensible!)
    (when extension-table-next
      (match-define (cons name maker) extension-table-next)
      (free-id-table-set! extension-table name maker)))

  (define (get-extensible name)
    (free-id-table-ref extension-table name (λ _ #f)))

  ;;

  (define extension-registry (make-free-id-table))

  (define (register-extension! base lang name)
    (define lang-table
      (free-id-table-ref! extension-registry base make-free-id-table))
    (free-id-table-set! lang-table lang name))

  (define (get-extension base lang)
    (define lang-table
      (free-id-table-ref extension-registry base (λ _ #f)))
    (and lang-table
         (free-id-table-ref lang-table lang (λ _ #f))))

  ;;

  (define (make-params lang params vals)
    (for/list ([param (in-syntax params)]
               [val (in-syntax vals)])
      (or (get-lang-extension param val lang)
          (get-lang-lifting param val lang))))

  #;(define (make-base-params ext params vals)
    (match-define (extensible base-params base-vals maker) ext)
    (define base-param-set
      (immutable-bound-id-set (syntax->list base-params)))
    (for/list ([param (in-syntax params)]
               [val (in-syntax vals)]
               #:when (bound-id-set-member? base-param-set param))
      (list param val)))

  #;(define (syntaxes->table base-params base-vals
                           params vals)
    (for/fold ([table (make-immutable-bound-id-table)])
              ([param (sequence-append (in-syntax base-params)
                                       (in-syntax params))]
               [val (sequence-append (in-syntax base-vals)
                                     (in-syntax vals))])
      (bound-id-table-set table param val)))

  (define (get-lang-extension param val lang)
    (define val* (get-extension val lang))
    (and val* (list param val* #'(void))))

  (define (get-lang-lifting param val lang)
    (define sc (make-syntax-introducer))
    (define val-sc (sc val))
    (define defn
      (replace-context
       val-sc
       ((extensible-maker (get-extensible val)) lang)))
    (list param val-sc defn))

  ;; add-extensible! is a terrible name
  (define (make-extensible name lang params vals defn)
    (define (maker lang)
      (define stx (make-params lang params vals))
      (with-syntax ([?lang lang]
                    [([?param ?val ?lift] ...) stx]
                    [?defn defn])
        #'(begin
            ?lift ...
            (splicing-let-syntax ([*LANG* (make-rename-transformer #'?lang)]
                                  [?param (make-rename-transformer #'?val)]
                                  ...)
              ?defn))))
    (define ext (extensible params vals maker))
    (set! extension-table-next (cons name ext))
    #`(begin
        #,(maker lang)
        (begin-for-syntax (add-extensible!))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax (define-reduction-relation* stx)
  (syntax-parse stx
    [(_ ?name:id ?lang:id ?p:params ?more ...)
     (make-extensible #'?name
                      #'?lang
                      #'(?p.param ...)
                      #'(?p.val ...)
                      #'(define-reduction-relation ?name
                          *LANG* ?more ...))]))

(define-syntax (define-extended-reduction-relation* stx)
  (syntax-parse stx
    [(_ ?name:id ?base:id ?lang:id ?p:params ?more ...)
     #:do [(define sc (make-syntax-introducer))]
     #:with ?base* (sc #'?base)
     #:with ?defn-base
     (replace-context
      #'?base*
      ((extensible-maker (get-extensible #'?base)) #'?lang))
     #:with ?defn-name
     (make-extensible #'?name
                      #'?lang
                      #'(?p.param ...)
                      #'(?p.val ...)
                      #'(define-extended-reduction-relation ?name
                          ?base* *LANG* ?more ...))
     #`(begin
         ?defn-base ?defn-name
         (begin-for-syntax
           (register-extension! #'?base #'?lang #'?name)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(begin-for-syntax
  (define-syntax-class mf-case
    (pattern [(name _ ...) _ ...])))

(define-syntax (define-metafunction* stx)
  (syntax-parse stx
    [(_ ?lang:id ?p:params ?more ... ?c:mf-case)
     #:with ?name #'?c.name
     (make-extensible #'?name
                      #'?lang
                      #'(?p.param ...)
                      #'(?p.val ...)
                      #'(define-metafunction
                          *LANG* ?more ... ?c))]))

(define-syntax (define-extended-metafunction* stx)
  (syntax-parse stx
    [(_ ?base:id ?lang:id ?p:params ?more ... ?c:mf-case)
     #:with ?name #'?c.name
     ;; TODO: share with lifting?
     #:do [(define sc (make-syntax-introducer))]
     #:with ?base* (sc #'?base)
     #:with ?defn-base
     (replace-context
      #'?base*
      ((extensible-maker (get-extensible #'?base)) #'?lang))
     #:with ?defn-name
     (make-extensible #'?name
                      #'?lang
                      #'(?p.param ...)
                      #'(?p.val ...)
                      #'(define-metafunction/extension
                          ?base *LANG* ?more ... ?c))
     #`(begin
         ?defn-base ?defn-name
         (begin-for-syntax
           (register-extension! #'?base #'?lang #'?name)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (define-reduction-relation ?name ?more ...)
  (define ?name (reduction-relation ?more ...)))

(define-syntax-rule (define-extended-reduction-relation ?name ?more ...)
  (define ?name (extend-reduction-relation ?more ...)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language L0
  [m ::= number])

(define-metafunction* L0
  [(L0-number m) 42])

(define-reduction-relation* r0
  L0
  #:parameters ([lang-number L0-number])
  [--> m (lang-number m)])

#;(apply-reduction-relation r0 (term 0))

(define-extended-language L1 L0
  [m ::= .... string])

#;(define-extended-metafunction* L0-number L1
  [(L1-number 1) 43])

(define-extended-reduction-relation* r1 r0 L1)

(apply-reduction-relation r1 (term "hi"))


#|
(define-extended-metafunction* L0-number L1
  [(L1-number 1) 43])

(define-extended-reduction-relation* r1
  r0 L1
  #:parameters ([new-thingy L1-number]))

(apply-reduction-relation r1 (term "hi"))
(apply-reduction-relation r1 (term 1))
|#
