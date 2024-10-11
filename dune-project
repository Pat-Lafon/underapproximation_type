(lang dune 3.14)

(using menhir 2.1)

(name underapproximation_type)

(package
 (name underapproximation_type)
 (depends
  dune
  (ocaml
   (= "4.14.2"))
  (core
   (<= "v0.16.2"))
  (core_unix
   (<= "v0.16.0"))
  (yojson
   (<= "1.7.0"))
  (z3
   (<= "4.13.0"))))
