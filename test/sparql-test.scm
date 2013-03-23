; TODO
; The piece below was moved from sparql.scm
; as it clearly belongs to a test suite,
; which should be written sooner or later.

; Example

'(
(define v (property-named "http://example.org/v"))
(define s (individual-named "http://example.org/s"))
(define o (individual-named "http://example.org/o"))

; > (v s o)
; '(vso (referent-of "data:x") (referent-of "data:s") (referent-of "data:o"))
; >
)
