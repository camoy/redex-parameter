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
                     racket/provide-transform
                     racket/sequence
                     racket/syntax
                     redex/private/term-fn
                     syntax/id-table
                     syntax/parse
                     syntax/strip-context)
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

  ;; Mode for a judgment.
  (define-syntax-class mode
    (pattern (name:id _ ...)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; redex object

(begin-for-syntax
  ;; An Automatic-Lift is a memoized expansion artifact containing its generated
  ;; identifier and the language generation under which it was built.
  (struct automatic-lift (id generation))

  ;; A Redex-Obj is a rename trasformer struct where
  ;;   [id : Identifier] is the defined identifier,
  ;;   [args : [Listof Syntax]] is the syntaxes needed for the maker,
  ;;   [exts : [Free-Id-Table Identifier]] maps languages to explicit semantic
  ;;     definitions, and
  ;;   [lifts : [Free-Id-Table Automatic-Lift]] maps languages to memoized
  ;;     automatic expansion artifacts.
  (struct redex-obj (id args exts lifts) #:property prop:rename-transformer 0)

  ;; Maps each language to the generation of its explicit semantic definitions.
  (define language-generations (make-free-id-table))

  ;; Identifier → Natural
  (define (language-generation lang)
    (free-id-table-ref language-generations lang (λ _ 0)))

  ;; Identifier → Any
  (define (advance-language-generation! lang)
    (free-id-table-set! language-generations
                        lang
                        (add1 (language-generation lang))))

  ;; Identifier Identifier Syntax Syntax Syntax →
  ;;   (Procedure Identifier → Identifier Syntax)
  ;; This will construct a "maker" from a bunch of syntaxes. The maker takes
  ;; a scope introducer and a language, and returns the identifier being defined
  ;; (with the scope attached) as well as the definition itself, at the provided
  ;; language.
  (define ((redex-obj-maker who name base params vals defn) sc lang)
    (define defn* (sc defn))
    (define base-stx
      (if (and (syntax? base) (syntax-e base))
          (list (cons (replace-context defn* #'*BASE*)
                      (lang-automatic-lift base lang)))
          null))
    (define param-stx (make-params params vals sc lang))
    (with-syntax ([?lang (replace-context defn* #'*LANG*)]
                  [([?base ?base* ?base-lift] ...) base-stx]
                  [([?param ?val ?lift] ...) param-stx])
      (values (sc name)
              #`(begin
                  ?base-lift ...
                  ?lift ...
                  (splicing-let-syntax ([?lang (make-rename-transformer #'#,lang)]
                                        [?base (make-rename-transformer #'?base*)]
                                        ...
                                        [?param (make-rename-transformer #'?val)]
                                        ...)
                    #,defn*)))))

  ;; Identifier Identifier Identifier Identifier Syntax Syntax Syntax → Syntax
  ;; Returns syntax that defines the object (according to `defn`) parameterized
  ;; appropriately for `lang`.
  (define (redex-obj-syntax who name base lang params vals defn)
    (define sc (make-syntax-introducer))
    (check-language lang (and who (syntax-e who)))
    (define maker (redex-obj-maker who name base params vals defn))
    (define-values (name* defn*) (maker sc lang))
    (define name** (syntax-property name* 'not-free-identifier=? #t))
    #`(begin
        #,defn*
        (define-syntax #,name
          (redex-obj #'#,name**
                     (list #'#,who
                           #'#,name
                           #'#,base
                           #'#,params
                           #'#,vals
                           #'((... ...) #,defn))
                     (make-free-id-table)
                     (make-free-id-table)))
        (begin-for-syntax
          (redex-obj-add-ext! #'#,name #'#,base #'#,lang))))

  ;; Syntax Symbol → Any
  ;; Checks that the identifier corresponds to a language.
  (define (check-language stx sym)
    (language-id-nts stx (or sym 'check-language)))

  ;; Procedure Identifier Syntax Syntax → [List Identifier Identifier Syntax]
  ;; Retrieves the list of the parameter, value for that parameter, and
  ;; definition; they are up to date for `lang`. Explicit semantic definitions
  ;; take precedence over memoized automatic lifts.
  (define (make-params params vals sc lang)
    (for/list ([param (in-syntax params)]
               [val (in-syntax vals)])
      (cons (sc param)
            (or (lang-extension val lang)
                (lang-automatic-lift val lang)))))

  ;; Identifier Identifier → [Or #f [List Identifier Syntax]]
  ;; If defined, returns the identifier for a user-defined extension.
  (define (lang-extension val lang)
    (define exts (redex-obj-exts (redex-obj-get val)))
    (define val* (free-id-table-ref exts lang (λ _ #f)))
    (and val* (list val* #'(void))))

  ;; Identifier Identifier → [List Identifier Syntax]
  ;; Reuses a memoized automatic lift when it was built under the current
  ;; language generation; otherwise rebuilds and caches it.
  (define (lang-automatic-lift val lang)
    (define lifts (redex-obj-lifts (redex-obj-get val)))
    (define generation (language-generation lang))
    (define cached (free-id-table-ref lifts lang (λ _ #f)))
    (cond
      [(and cached (= (automatic-lift-generation cached) generation))
       (list (automatic-lift-id cached) #'(void))]
      [else
       (define result (lift val lang))
       (free-id-table-set! lifts
                           lang
                           (automatic-lift (car result) generation))
       result]))

  ;; Identifier Identifier → [List Identifier Syntax]
  ;; Returns the syntax needed to lift the value to this language.
  (define (lift id lang)
    (define args (redex-obj-args (redex-obj-get id)))
    (define sc (make-syntax-introducer))
    (define-values (lifted-id lifted-defn)
      ((apply redex-obj-maker args) sc lang))
    (list lifted-id lifted-defn))

  ;; Identifier → Redex-Obj
  ;; Gets the Redex object associated with the given identifier.
  (define (redex-obj-get id)
    (define-values (obj _)
      (syntax-local-value/immediate id (λ _ (values #f #f))))
    (unless (redex-obj? obj)
      (define MSG
        (string-append "not defined as liftable; "
                       "use the * version of define"))
      (raise-syntax-error #f MSG id))
    obj)

  ;; Identifier Identifier Identifier → Any
  ;; Register an explicit semantic definition and advance its language's
  ;; generation, invalidating memoized automatic lifts for that language.
  (define (redex-obj-add-ext! name base lang)
    (when (syntax-e base)
      (define exts (redex-obj-exts (redex-obj-get base)))
      (free-id-table-set! exts lang name)
      (advance-language-generation! lang)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reduction relation

(define-syntax-rule (define-reduction-relation ?name ?more ...)
  (define ?name (reduction-relation ?more ...)))

(define-syntax-rule (define-extended-reduction-relation ?name ?more ...)
  (define ?name (extend-reduction-relation ?more ...)))

(define-syntax (define-reduction-relation* stx)
  (syntax-parse stx
    [(?who:id ?name:id ?lang:id ?p:params ?more ...)
     (redex-obj-syntax #'?who
                       #'?name
                       #f
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-reduction-relation ?name
                           *LANG* ?more ...))]))

(define-syntax (define-extended-reduction-relation* stx)
  (syntax-parse stx
    [(?who:id ?name:id ?base:id ?lang:id ?p:params ?more ...)
     (redex-obj-syntax #'?who
                       #'?name
                       #'?base
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-extended-reduction-relation ?name
                           *BASE* *LANG* ?more ...))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; metafunction

(define-syntax-rule (define-extended-metafunction ?more ...)
  (define-metafunction/extension ?more ...))

(define-syntax (define-metafunction* stx)
  (syntax-parse stx
    [(?who:id ?lang:id ?p:params ?name:id ?more ...)
     (redex-obj-syntax #'?who
                       #'?name
                       #f
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-metafunction
                           *LANG* ?name ?more ...))]))

(define-syntax (define-extended-metafunction* stx)
  (syntax-parse stx
    [(?who:id ?base:id ?lang:id ?p:params ?name:id ?more ...)
     (redex-obj-syntax #'?who
                       #'?name
                       #'?base
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-extended-metafunction
                           *BASE* *LANG* ?name ?more ...))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; judgment form

(define-syntax (define-judgment-form* stx)
  (syntax-parse stx
    [(?who:id ?lang:id ?p:params #:mode ?m:mode ?more ...)
     #:with ?name #'?m.name
     (redex-obj-syntax #'?who
                       #'?name
                       #f
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-judgment-form
                           *LANG* #:mode ?m ?more ...))]))

(define-syntax (define-extended-judgment-form* stx)
  (syntax-parse stx
    [(?who:id ?base:id ?lang:id #:mode ?m:mode ?p:params ?more ...)
     #:with ?name #'?m.name
     (redex-obj-syntax #'?who
                       #'?name
                       #'?base
                       #'?lang
                       #'(?p.param ...)
                       #'(?p.val ...)
                       #'(define-extended-judgment-form
                           *LANG* *BASE* #:mode ?m ?more ...))]))
