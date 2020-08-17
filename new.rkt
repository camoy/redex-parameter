#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; provide

(provide define-reduction-relation
         define-extended-reduction-relation
         define-reduction-relation*
         define-extended-reduction-relation*
         define-extended-metafunction
         define-metafunction*
         define-extended-metafunction*
         define-judgment-form*
         define-extended-judgment-form*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; require

(require (for-syntax racket/base
                     racket/match
                     racket/sequence
                     syntax/id-table
                     syntax/parse
                     syntax/strip-context)
         racket/splicing
         redex/reduction-semantics)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; syntax classes

(begin-for-syntax
  (define-splicing-syntax-class params
    (pattern (~seq #:parameters ([param:id val:id] ...)))
    (pattern (~seq)
             #:attr (param 1) null
             #:attr (val 1) null))

  (define-syntax-class mf-case
    (pattern [(name:id _ ...) _ ...]))

  (define-syntax-class mode
    (pattern (name:id _ ...)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compile-time tables

(begin-for-syntax
  (define maker-table (make-free-id-table))

  (define (add-maker! id maker)
    (free-id-table-set! maker-table id maker))

  (define (apply-maker id lang)
    (define (not-found)
      (error 'redex-parameter
             (string-append  "~a was not defined as extensible; "
                             "use the * version of define")
             (syntax-e id)))
    (define maker
      (free-id-table-ref maker-table id not-found))
    (maker lang))

  (define extension-table (make-free-id-table))

  (define (add-extension! base lang name)
    (define lang-table
      (free-id-table-ref! extension-table base make-free-id-table))
    (free-id-table-set! lang-table lang name))

  (define (get-extension base lang)
    (define lang-table
      (free-id-table-ref extension-table base (λ _ #f)))
    (and lang-table
         (free-id-table-ref lang-table lang (λ _ #f))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; generic parameterized syntax

(begin-for-syntax
  (define (redex-form-syntax name lang params vals defn)
    (define (maker lang)
      (define stx (make-params lang params vals))
      (with-syntax ([([?param ?val ?lift] ...) stx])
        #`(begin
            ?lift ...
            (splicing-let-syntax ([*LANG* (make-rename-transformer #'#,lang)]
                                  [?param (make-rename-transformer #'?val)]
                                  ...)
              #,defn))))
    #`(begin
        #,(maker lang)
        (begin-for-syntax (add-maker! #'#,name #,maker))))

  (define (make-params lang params vals)
    (for/list ([param (in-syntax params)]
               [val (in-syntax vals)])
      (or (get-lang-extension param val lang)
          (get-lang-lifting param val lang))))

  (define (get-lang-extension param val lang)
    (define val* (get-extension val lang))
    (and val* (list param val* #'(void))))

  (define (get-lang-lifting param val lang)
    (cons param (lift val lang)))

  (define (lift id lang)
    (define sc (make-syntax-introducer))
    (define id* (sc id))
    (define defn (replace-context id* (apply-maker id lang)))
    (list id* defn))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reduction relation

(define-syntax-rule (define-reduction-relation ?name ?more ...)
  (define ?name (reduction-relation ?more ...)))

(define-syntax-rule (define-extended-reduction-relation ?name ?more ...)
  (define ?name (extend-reduction-relation ?more ...)))

(define-syntax (define-reduction-relation* stx)
  (syntax-parse stx
    [(_ ?name:id ?lang:id ?p:params ?more ...)
     (redex-form-syntax #'?name
                        #'?lang
                        #'(?p.param ...)
                        #'(?p.val ...)
                        #'(define-reduction-relation ?name
                            *LANG* ?more ...))]))

(define-syntax (define-extended-reduction-relation* stx)
  (syntax-parse stx
    [(_ ?name:id ?base:id ?lang:id ?p:params ?more ...)
     #:with [?base* ?defn-base] (lift #'?base #'?lang)
     #:with ?defn-form
     (redex-form-syntax #'?name
                        #'?lang
                        #'(?p.param ...)
                        #'(?p.val ...)
                        #'(define-extended-reduction-relation ?name
                            ?base* *LANG* ?more ...))
     #`(begin
         ?defn-base ?defn-form
         (begin-for-syntax (add-extension! #'?base #'?lang #'?name)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; metafunction

(define-syntax-rule (define-extended-metafunction ?more ...)
  (define-metafunction/extension ?more ...))

(define-syntax (define-metafunction* stx)
  (syntax-parse stx
    [(_ ?lang:id ?p:params ?more ... ?c:mf-case)
     #:with ?name #'?c.name
     (redex-form-syntax #'?name
                        #'?lang
                        #'(?p.param ...)
                        #'(?p.val ...)
                        #'(define-metafunction
                            *LANG* ?more ... ?c))]))

(define-syntax (define-extended-metafunction* stx)
  (syntax-parse stx
    [(_ ?base:id ?lang:id ?p:params ?more ... ?c:mf-case)
     #:with ?name #'?c.name
     #:with [?base* ?defn-base] (lift #'?base #'?lang)
     #:with ?defn-form
     (redex-form-syntax #'?name
                        #'?lang
                        #'(?p.param ...)
                        #'(?p.val ...)
                        #'(define-extended-metafunction
                            ?base* *LANG* ?more ... ?c))
     #`(begin
         ?defn-base ?defn-form
         (begin-for-syntax (add-extension! #'?base #'?lang #'?name)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; judgment form

(define-syntax (define-judgment-form* stx)
  (syntax-parse stx
    [(_ ?lang:id ?p:params #:mode ?m:mode ?more ...)
     #:with ?name #'?m.name
     (redex-form-syntax #'?name
                        #'?lang
                        #'(?p.param ...)
                        #'(?p.val ...)
                        #'(define-judgment-form
                            *LANG* #:mode ?m ?more ...))]))

(define-syntax (define-extended-judgment-form* stx)
  (syntax-parse stx
    [(_ ?base:id ?lang:id #:mode ?m:mode ?p:params ?more ...)
     #:with ?name #'?m.name
     #:with [?base* ?defn-base] (lift #'?base #'?lang)
     #:with ?defn-form
     (redex-form-syntax #'?name
                        #'?lang
                        #'(?p.param ...)
                        #'(?p.val ...)
                        #'(define-extended-judgment-form
                            *LANG* ?base* #:mode ?m ?more ...))
     #`(begin
         ?defn-base ?defn-form
         (begin-for-syntax (add-extension! #'?base #'?lang #'?name)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test

(module+ test
  (require chk
           racket/set)

  ;;
  ;; Languages
  ;;

  (define-language L0
    [m ::= number])

  (define-language L1
    [m ::= number string])

  ;;
  ;; Reduction Relations
  ;;

  (define-metafunction* L0
    [(foo-mf0 m) 0])

  (define-judgment-form* L0
    #:mode (foo-jf0 I O)
    [(foo-jf0 m 0)])

  (define-reduction-relation* r0-mf
    L0
    #:parameters ([foo-mf foo-mf0])
    [--> m (foo-mf m)])

  (define-reduction-relation* r0-jf
    L0
    #:parameters ([foo-jf foo-jf0])
    [--> m_1 m_2 (judgment-holds (foo-jf m_1 m_2))])

  (define-reduction-relation* r0-rr
    L0
    #:parameters ([r r0-mf])
    [--> m_1 m_2
         (where (_ ... m_2 _ ...)
                ,(apply-reduction-relation r (term m_1)))])

  (chk
   (apply-reduction-relation r0-mf (term 42)) '(0)
   (apply-reduction-relation r0-jf (term 42)) '(0)
   (apply-reduction-relation r0-rr (term 42)) '(0)
   )

  ;;
  ;; Reduction Relation (lifted)
  ;;

  (define-extended-reduction-relation* r1-mf r0-mf L1)
  (define-extended-reduction-relation* r1-jf r0-jf L1)
  (define-extended-reduction-relation* r1-rr r0-rr L1)

  (chk
   (apply-reduction-relation r1-mf (term "foo")) '(0)
   (apply-reduction-relation r1-jf (term "foo")) '(0)
   (apply-reduction-relation r1-rr (term "foo")) '(0)
   )

  ;;
  ;; Reduction Relation (extended)
  ;;

  (define-extended-metafunction* foo-mf0 L1
    [(foo-mf1 m) 1.5])

  (define-extended-judgment-form* foo-jf0 L1
    #:mode (foo-jf1 I O)
    [(foo-jf1 m 1.5)])

  (define-extended-reduction-relation* r1.5-mf r0-mf L1)
  (define-extended-reduction-relation* r1.5-jf r0-jf L1)
  (define-extended-reduction-relation* r1.5-rr r0-rr L1)

  (chk
   (apply-reduction-relation r1.5-mf (term "foo")) '(1.5)
   #:eq set=? (apply-reduction-relation r1.5-jf (term "foo")) '(0 1.5)
   (apply-reduction-relation r1.5-rr (term "foo")) '(1.5)
   )

  ;;
  ;; Judgment Form
  ;;

  (define-metafunction* L0
    [(bar-mf0 m) 0])

  (define-judgment-form* L0
    #:parameters ([bar-mf bar-mf0])
    #:mode (bar-jf0 I O)
    [(bar-jf0 m (bar-mf m))])

  (define-extended-judgment-form* bar-jf0 L1
    #:mode (bar-jf1 I O))

  (chk
   #:t (judgment-holds (bar-jf0 0 0))
   #:t (judgment-holds (bar-jf1 "bar" 0))
   ))
