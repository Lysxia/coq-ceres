(lang dune 2.8)
(using coq 0.3)
(name coq-ceres)
(version dev)

(generate_opam_files true)

(source (github Lysxia/coq-ceres))
(license MIT)
(authors "Li-yao Xia")
(maintainers "lysxia@gmail.com")

(package
 (name coq-ceres)
 (synopsis "Library for serialization via S-expressions")
 (depends (coq (>= 8.8~)))
)
