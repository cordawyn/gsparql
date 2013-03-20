; In this theory of SPARQL, we have 'predicates' which are n-place
; abstractions of statements (or graphs).  A one-place predicate is
; a class and a two-place predicate is a property.  A SPARQL SELECT
; is an n-place predicate where n = the number of variables (columns
; in result set).
;

; Scheme procedures represent predicates and records called
; 'doppelgangers' represent the individuals to which predicates apply.

; If C is a class-procedure and P is a property-procedure then the
; Scheme expressions
;   (class thing)
;   (property thing1 thing2)
; evaluate to structures that can be transliterated into Turtle.
; Similarly, the Scheme procedure
;   (predicate (?x ?y) ... ?x ... ?y ...)
; (where the body is an implicit conjunction) evaluates to something
; that can be rendered as a SPARQL SELECT.

(use-modules (srfi srfi-9))
(use-modules (srfi srfi-9 gnu))

; Better to have separate creators for individuals, classes, and properties

; The doppelganger is not the thing itself, but rather a Scheme object
; that, inside the Scheme address space, stands for the thing

(define-record-type :doppelganger
  (make-doppelganger term)
  doppelganger?
  (term doppelganger->term))

(set-record-type-printer! :doppelganger
  (lambda (d) `(referent-of ,(doppelganger->term d))))

; Write as Turtle or SPARQL
; In the future, maybe, make this exploit namespaces
; TBD: worry about escaping (a URI containing >, \, or ")

(define (write-doppelganger d port)
  (display (doppelganger->term d) port))

(define (unterm term)
  (let ((match (string-match "^<(.*)>$" term)))
    (if match
      (match:substring match 1)
      term)))

;; (define unterm
;;   (let ((reg (regex "^<(.*)>$")))
;;     (lambda (term)
;;       (let ((match (regex-match reg term)))
;;	(if match
;;	    (*:get match 1)  ;; "regex-match" returns a java.util.LinkedList, gah.
;;	    term)))))

(define (contract ns uri)
  (ns 'contract uri))

(define (undoppel v)
  (if (doppelganger? v)
      (doppelganger->term v)
      v))

; Consider alternative name <> since that's how it's written in N3

(define (referent-of uri)
  (make-doppelganger (string-append "<" uri ">")))

(define (individual-named uri)
  (referent-of uri))

; property = two-place predicate

(define (property-named uri)
  (let ((r (referent-of uri)))
    (lambda args
      (cond ((null? args)
	     ;; (foo) => "http://baz/foo"
	     r)
	    ((null? (cdr args))
	     (error "wrong number of arguments" uri args))
	    ((null? (cddr args))
	     (list 'vso
		   r
		   (subject-term (car args))
		   (subject-term (cadr args))))
	    (else (error "too many arguments" uri args))))))

(define (subject-term thing)
  (if (procedure? thing)
      (thing)
      ;; URI, literal, or blank-node notation
      thing))

; class = one-place predicate

(define has-type
  (property-named "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"))

(define (class-named uri)
  (let ((r (referent-of uri)))
    (lambda args
      (cond ((null? args)
	     ;; (foo) => "http://baz/foo"
	     r)
	    ((null? (cdr args))
	     (has-type (car args) r))
	    (else (error "too many arguments" uri args))))))

; Implicit AND of a query body or a graph

(define (conjunction . statements)
  (if (and (pair? statements)
	   (null? (cdr statements)))
      (car statements)
      `(conjunction ,@statements)))

(define (union . statements)
  (if (and (pair? statements)
	   (null? (cdr statements)))
      (car statements)
      `(union ,@statements)))

(define (write-statement stmt port)
  (case (car stmt)
    ((vso) (write-vso stmt port))
    ((conjunction)
     (for-each (lambda (stmt) (write-statement stmt port))
	       (cdr stmt)))
    ((union)
     (begin
       (let ((blocks (map (lambda (stmt)
			    (let* ((strport (open-output-string))
				   (body (write-statement stmt strport)))
			      (string-append "{ " (get-output-string strport) " }")))
			  (cdr stmt))))
	 (display (fold (lambda (b1 b2)
			  (string-append b1 " UNION " b2))
			""
			blocks)
		  port))))
    (else
     (error "inscrutable statement" stmt))))

; Statements can be rendered in Turtle
; Compare packages/common/scheme/rdf.sch

(define (write-vso vso port)
  (write-nonliteral-term (caddr vso) port)	;Subject goes first in Turtle
  (display " " port)
  (write-nonliteral-term (cadr vso) port)	;then verb
  (display " " port)
  (write-term (cadddr vso) port)	;object can be a literal
  (display " ." port)
  (newline port))

; Add error checks later

(define (write-nonliteral-term term port)
  (write-term term port))

; TBD: handle blank-node notation / Skolemization

(define (write-term term port)
  (cond ((doppelganger? term)
	 (write-doppelganger term port))
	((string? term)
	 ;; this handles ordinary string cases, but is obviously fragile
	 (write term port))
	((and (integer? term) (exact? term))
	 ;; integers are understood natively by SPARQL and Turtle, I think
	 (write term port))
	((symbol? term)
	 ;; we get here if term is a SPARQL variable or blank node name.  pass on through
	 (write term port))
	(else
	 (error "this kind of literal isn't implemented" term))))

; Example

'(
(define v (property-named "http://example.org/v"))
(define s (individual-named "http://example.org/s"))
(define o (individual-named "http://example.org/o"))

; > (v s o)
; '(vso (referent-of "data:x") (referent-of "data:s") (referent-of "data:o"))
; >
)

;-----------------------------------------------------------------------------
; TBD: blank nodes.  These should exploit the predicate abstraction, below


;-----------------------------------------------------------------------------

; SPARQL

; predicate ~= lambda

(define-syntax predicate
  (syntax-rules ()
    ((predicate (?var ...) ?statement ...)
     (%make-predicate '(?var ...)
		      (lambda (?var ...)
			(conjunction ?statement ...))))))

; Kludge - this rules out 0-ary predicates (sparql 'ask').  Maybe fix later.

(define (%make-predicate vars proc)
  (lambda args
    (if (null? args)
	`(predicate ,vars
		    ,(apply proc
			    (map variable->doppelganger vars)))
	(apply proc args))))

; This is complicated by queries like (?v ?s ?o)

(define (variable->doppelganger symbol)
  (let ((r (make-doppelganger (symbol->string symbol))))
    (lambda args
      (cond ((null? args) r)
	    ((null? (cdr args))
	     (has-type (car args) r))
	    ((null? (cddr args))
	     (list 'vso
		   r
		   (subject-term (car args))
		   (subject-term (cadr args))))
	    (else (error "too many arguments" symbol args))))))

; Write a predicate as a SPARQL SELECT

(define (write-predicate-as-select pred port distinct? limit)
  (let ((pred-form (pred)))
    (if (or (not (pair? pred-form)) (not (eq? (car pred-form) 'predicate)))
	;; In the future maybe liberalize this by eta-expansion, so that pred
	;; can be a predicate returned by 'property-named' or 'class-named'
	(error "attempt to use non-predicate as query" pred))
    (let ((vars (cadr pred-form))
	  (body (caddr pred-form)))
      (display "select" port)
      (if distinct?
	  (display " distinct" port)
	  #f)
      (for-each (lambda (var) (display " " port) (write var port))
		vars)
      (newline port)
      (display "where {" port)
      (newline port)
      (write-statement body port)
      (display "}" port)
      (if (and limit (> limit 1))
	  (begin (display " limit " port)
		 (write limit port))
	  #f)
      (newline port))))

(define (pred->select pred distinct? limit)
  (let ((port (open-output-string)))
    (write-predicate-as-select pred port distinct? limit)
    (get-output-string port)))

(define (web-endpoint name)
  (<org.neurocommons.sparql.QueryManager>:createEndpoint name))

(define (raw-query endpoint querystring)
  (*:executeQuery endpoint querystring))

(define (as-prefix ns)
  (string-append
   "prefix " (ns 'contract (ns))
   " <" (ns) ">"))

(define (ns-query querystring . namespaces)
  (let ((header (fold-right (curry string-append " ") "" (map as-prefix namespaces))))
    (string-append header " " querystring)))

(define (qq endpoint query . namespaces)
  (parse-raw-query endpoint
		   (raw-query endpoint (apply ns-query (cons query namespaces)))))

(define (parse-raw-query endpoint resultstring)
  (parse-query-results
   (*:parseQuery endpoint
		 (string->symbol resultstring))))

(define (pose-query endpoint predicate distinct? limit)
  (let ((queryout (open-output-string)))
    (write-predicate-as-select predicate queryout distinct? limit)
    (parse-query-results
     (*:parseQuery endpoint
		   (*:executeQuery endpoint (get-output-string queryout))))))


(load "proc-utils.sch")

(define resultify
  (compose (listify unterm) (listify undoppel)))

(define (parse-query-results array)
  (let ((indices (numseq 0 (- (*:.length array) 1))))
    (map (lambda (idx) (parse-result (array idx))) indices)))

(define (numseq min max)
  (if (<= min max)
      (cons min (numseq (+ 1 min) max))
      '()))

(define (parse-result result)
  (let ((indices (numseq 0 (- (*:length result) 1))))
    (map (lambda (idx) (parse-term (*:getTerm result idx)))
	 indices)))

(define (parse-term term)
  (cond
	((*:isLiteral term) (*:toString term))
	((*:isURI term) (individual-named (*:toString term)))
	((*:isBlankNode term) (bnode-named (*:toString term)))
	(_ '())))
