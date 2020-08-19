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
                     syntax/parse)
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
  ;; Maps a Redex object identifier to a constructor for that object.
  (define maker-table (make-free-id-table))

  ;; → Any
  ;; Adds a constructor for a Redex object.
  (define (add-maker! id)
    (define xs (syntax-local-value id (λ _ #f)))
    (when xs
      (define name (car xs))
      (free-id-table-set! maker-table name (apply do-maker xs))))

  ;; Identifier Procedure Identifier → Syntax
  ;; Returns the syntax needed to define the object `id` for `lang`.
  (define (apply-maker id sc lang)
    (define (not-found)
      (error 'redex-parameter
             (string-append  "~a was not defined as liftable; "
                             "use the * version of define")
             (syntax-e id)))
    (add-maker! (format-mk id))
    (define maker (free-id-table-ref maker-table id not-found))
    (maker sc lang))

  ;; [Free-Id-Table Identifier [Free-Id-Table Identifier Identifier]
  ;; A two-level table mapping a Redex object identifier and a language to
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
  ;; Identifier → Identifier
  ;; Returns the identifier for recording a `maker-table` entry.
  (define (format-mk x)
    (format-id x "~a-mk-table" x))

  ;; Identifier → Identifier
  ;; Returns the identifier for recording an `extension-table` entry.
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
  ;; Identifier Syntax Syntax Syntax → (Procedure Identifier → Identifier Syntax)
  ;; This will construct a "maker" from a bunch of syntaxes. The maker takes
  ;; a scope introducer and a language, and returns the identifier being defined
  ;; (with the scope attached) as well as the definition itself, for the provided
  ;; language.
  (define ((do-maker name params vals defn) sc lang)
    (define stx (make-params sc lang params vals))
    (with-syntax ([?lang (sc #'*LANG*)]
                  [([?param ?val ?lift] ...) stx])
      (values
       (sc name)
       #`(begin
           ?lift ...
           (splicing-let-syntax ([?lang (make-rename-transformer #'#,lang)]
                                 [?param (make-rename-transformer #'?val)]
                                 ...)
             #,(sc defn))))))

  ;; Identifier Identifier Identifier Syntax Syntax Syntax → Syntax
  ;; Returns syntax that defines the object (according to `defn`) parameterized
  ;; appropriately for `lang`.
  (define (redex-obj-syntax name base lang params vals defn)
    (define mk-id (format-mk name))
    (define ext-id (format-ext name))
    (define-values (_ stx) ((do-maker name params vals defn) values lang))
    #`(begin
        ;; Definition
        #,stx

        ;; For maker table
        (define-syntax #,mk-id
          (list #'#,name #'#,params #'#,vals #'((... ...) #,defn)))
        (begin-for-syntax (add-maker! #'#,mk-id))

        ;; For extension table
        (define-syntax #,ext-id
          #,(if base
                #`(list #'#,base #'#,lang #'#,name)
                #'#f))
        (begin-for-syntax (add-extension! #'#,ext-id))))

  ;; Procedure Identifier Syntax Syntax → [List Identifier Identifier Syntax]
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
    (define-values (defn-id defn) (apply-maker id sc lang))
    (list defn-id defn))
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
