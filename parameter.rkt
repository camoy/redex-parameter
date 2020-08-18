#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; provide

(provide redex-out
         define-reduction-relation
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
                     racket/provide-transform
                     racket/sequence
                     racket/syntax
                     syntax/id-table
                     syntax/parse
                     syntax/strip-context
                     racket/pretty)
         racket/splicing
         redex/reduction-semantics)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; syntax classes

(begin-for-syntax
  ;; For parsing the `define-...*` forms.
  (define-splicing-syntax-class params
    (pattern (~seq #:parameters ([param:id val:id] ...)))
    (pattern (~seq)
             #:attr (param 1) null
             #:attr (val 1) null))

  ;; For extracting the name from a metafunction.
  (define-syntax-class mf-case
    (pattern [(name:id _ ...) _ ...]))

  ;; Similar, but for a judgment.
  (define-syntax-class mode
    (pattern (name:id _ ...)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compile-time tables

(begin-for-syntax
  ;; [Free-Id-Table Identifier Procedure]
  ;; Maps a redex object identifier to a constructor for that object.
  (define maker-table (make-free-id-table))

  ;; → Any
  ;; Adds a constructor for a redex object.
  (define (add-maker! id)
    (define xs (syntax-local-value id (λ _ #f)))
    (when xs
      (match-define (list name params vals defn) xs)
      (free-id-table-set! maker-table name (do-maker params vals defn))))

  ;; Identifier Identifier → Syntax
  ;; Returns the syntax needed to define the object `id` for `lang`.
  (define (apply-maker id sc lang)
    (define (not-found)
      (error 'redex-parameter
             (string-append  "~a was not defined as extensible; "
                             "use the * version of define")
             (syntax-e id)))
    (add-maker! (format-mk id))
    (define maker (free-id-table-ref maker-table id not-found))
    (maker sc lang))

  ;; [Free-Id-Table Identifier [Free-Id-Table Identifier Identifier]
  ;; A two-level table mapping a redex object identifier and a language to
  ;; the identifier that extends it for that language.
  (define extension-table (make-free-id-table))

  ;; Identifier → Any
  ;; Add the given extension to the table of extensions.
  (define (add-extension! id)
    (define xs (syntax-local-value id (λ _ #f)))
    (when xs
      (match-define (list base lang name) xs)
      (define lang-table
        (free-id-table-ref! extension-table base make-free-id-table))
      (free-id-table-set! lang-table lang name)))

  ;; Identifier Identifier → Identifier
  ;; Retrieves the most recent extension of `base` for `lang`.
  (define (get-extension base lang)
    (add-extension! (format-ext base))
    (define lang-table
      (free-id-table-ref extension-table base (λ _ #f)))
    (and lang-table
         (free-id-table-ref lang-table lang (λ _ #f))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; provide transformer

(begin-for-syntax
  ;; TODO
  (define (format-mk x)
    (format-id x "~a-mk-table" x))

  ;; TODO
  (define (format-ext x)
    (format-id x "~a-ext-table" x))
  )

;; Provide transformer for exporting the maker and extension tables.
(define-syntax redex-out
  (make-provide-transformer
   (λ (stx modes)
     (syntax-parse stx
       [(_ ?x:id ...)
        #:do [(define xs (syntax->list #'(?x ...)))]
        #:with (?x-mk ...) (map format-mk xs)
        #:with (?x-ext ...) (map format-ext xs)
        (expand-export
         #'(combine-out ?x ... ?x-mk ... ?x-ext ...)
         '())]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; generic parameterized syntax

(begin-for-syntax
  (define ((do-maker params vals defn) sc lang)
    (define stx (make-params sc lang params vals))
    (with-syntax ([?lang (sc #'*LANG*)]
                  [([?param ?val ?lift] ...) stx])
      #`(begin
          ?lift ...
          (splicing-let-syntax ([?lang (make-rename-transformer #'#,lang)]
                                [?param (make-rename-transformer #'?val)]
                                ...)
            #,(sc defn)))))

  ;; Identifier Identifier Syntax Syntax Syntax → Syntax
  ;; Returns syntax that defines the object (according to `defn`) parameterized
  ;; appropriately for `lang`.
  (define (redex-obj-syntax name base lang params vals defn)
    (define mk-id (format-mk name))
    (define ext-id (format-ext name))
    #`(begin
        #,((do-maker params vals defn) values lang)

        (define-syntax #,mk-id
          (list #'#,name #'#,params #'#,vals #'((... ...) #,defn)))
        (begin-for-syntax (add-maker! #'#,mk-id))

        (define-syntax #,ext-id
          #,(if base
                #`(list #'#,base #'#,lang #'#,name)
                #'#f))
        (begin-for-syntax (add-extension! #'#,ext-id))))

  ;; Identifier Syntax Syntax → [List Identifier Identifier Syntax]
  ;; Retrieves the a list of the parameter, value for that parameter, and
  ;; definition, that is up to date for `lang`. This will either retrieving
  ;; an extension, or lifting the value.
  (define (make-params sc lang params vals)
    (for/list ([param (in-syntax params)]
               [val (in-syntax vals)])
      (cons (sc param)
            (or (lang-extension val lang)
                (lift val lang)))))

  ;; Identifier Identifier → [Or #f [List Identifier Syntax]]
  ;; If defined, returns the identifier for a user-defined extension.
  (define (lang-extension val lang)
    (define val* (get-extension val lang))
    (and val* (list val* #'(void))))

  ;; Identifier Identifier → [List Identifier Syntax]
  ;; Returns the syntax needed to lift the value to this language.
  (define (lift id lang)
    (define sc (make-syntax-introducer))
    (define id* (sc id))
    (define (sc* stx) (replace-context id* stx))
    (define defn (apply-maker id sc* lang))
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
     (redex-obj-syntax #'?name
                       #f
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
     (redex-obj-syntax #'?name
                       #'?base
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-extended-reduction-relation ?name
                           ?base* *LANG* ?more ...))
     (define ext-id (format-ext #'?name))
     #`(begin ?defn-base ?defn-form)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; metafunction

(define-syntax-rule (define-extended-metafunction ?more ...)
  (define-metafunction/extension ?more ...))

(define-syntax (define-metafunction* stx)
  (syntax-parse stx
    [(_ ?lang:id ?p:params ?more ... ?c:mf-case)
     #:with ?name #'?c.name
     (redex-obj-syntax #'?name
                       #f
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
     (redex-obj-syntax #'?name
                       #'?base
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-extended-metafunction
                           ?base* *LANG* ?more ... ?c))
     #`(begin ?defn-base ?defn-form)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; judgment form

(define-syntax (define-judgment-form* stx)
  (syntax-parse stx
    [(_ ?lang:id ?p:params #:mode ?m:mode ?more ...)
     #:with ?name #'?m.name
     (redex-obj-syntax #'?name
                       #f
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
     (redex-obj-syntax #'?name
                       #'?base
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-extended-judgment-form
                           *LANG* ?base* #:mode ?m ?more ...))
     #`(begin ?defn-base ?defn-form)]))

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
