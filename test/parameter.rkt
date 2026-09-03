#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; require

(require redex/reduction-semantics
         redex/parameter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test

(module+ test
  (provide L0 L1
           foo-mf0 foo-jf0
           r0-mf r0-jf r0-rr)

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

  ;; This is to make sure that locally-defined identifiers are correctly
  ;; exported.
  (define (identity x) x)

  (define-metafunction* L0
    foo-mf0 : m -> m
    [(foo-mf0 m) ,(identity 0)])

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
    foo-mf1 : m -> m
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
    bar-mf0 : m -> m
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
   )

  ;;
  ;; Extended Bases
  ;;

  (define-language B0
    [e ::= natural])

  (define-language B1
    [e ::= natural string])

  (define-language B2
    [e ::= natural string boolean])

  (define-metafunction* B0
    base-leaf : e -> e
    [(base-leaf e) 0])

  (define-metafunction* B0 #:parameters ([current-leaf base-leaf])
    base-mf : e -> e
    [(base-mf e) (current-leaf e)])

  (define-reduction-relation* base-rr
    B0
    #:parameters ([current-leaf base-leaf])
    [--> e (current-leaf e)])

  (define-judgment-form* B0
    #:parameters ([current-leaf base-leaf])
    #:mode (base-jf I O)
    [(base-jf e (current-leaf e))])

  (define-extended-metafunction* base-mf B1
    middle-mf : e -> e
    [(middle-mf "middle") "middle"])

  (define-extended-reduction-relation* middle-rr base-rr B1)

  (define-extended-judgment-form* base-jf B1
    #:mode (middle-jf I O))

  (define-extended-metafunction* base-leaf B2
    final-leaf : e -> e
    [(final-leaf e) 1])

  (define-extended-metafunction* middle-mf B2
    final-mf : e -> e
    [(final-mf #t) #t])

  (define-extended-reduction-relation* final-rr middle-rr B2)

  (define-extended-judgment-form* middle-jf B2
    #:mode (final-jf I O))

  (chk
   (term (final-mf 42)) 1
   (apply-reduction-relation final-rr (term 42)) '(1)
   (judgment-holds (final-jf 42 e) e) '(1)
   )

  ;;
  ;; Ancestor Extensions
  ;;

  (define-language A
    [e ::= natural])

  (define-metafunction* A
    root : e -> e
    [(root e) 0])

  (define-extended-metafunction* root A
    child : e -> e
    [(child e) 1])

  (define-extended-metafunction* child A
    grandchild : e -> e
    [(grandchild e) 2])

  (define-metafunction* A #:parameters ([current-root root])
    through-root : e -> e
    [(through-root e) (current-root e)])

  (chk
   (term (through-root 42)) 2
   )

  ;;
  ;; From Jason
  ;;

  (define-language M
    [e ::= natural])

  (define-metafunction* M
    leaf : e -> e
    [(leaf e) 0])

  (define-metafunction* M #:parameters ([current-leaf leaf])
    middle : e -> e
    [(middle e) (current-leaf e)])

  (define-metafunction* M #:parameters ([current-middle middle])
    before : e -> e
    [(before e) (current-middle e)])

  (define-extended-metafunction* leaf M
    new-leaf : e -> e
    [(new-leaf e) 1])

  (define-metafunction* M #:parameters ([current-leaf leaf])
    direct : e -> e
    [(direct e) (current-leaf e)])

  (define-metafunction* M #:parameters ([current-middle middle])
    after : e -> e
    [(after e) (current-middle e)])

  (chk
   (term (direct 42)) 1
   (term (after 42)) 1
   )

  ;; A second explicit extension must invalidate the transitive automatic lift
  ;; of `middle` cached while defining `after`.
  (define-extended-metafunction* leaf M
    newer-leaf : e -> e
    [(newer-leaf e) 2])

  (define-metafunction* M #:parameters ([current-middle middle])
    after-again : e -> e
    [(after-again e) (current-middle e)])

  (chk
   (term (after-again 42)) 2
   ))
