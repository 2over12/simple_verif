(lang dune 3.8)

(name simple_verif)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(using menhir 2.1)

(package
 (name simple_verif)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune containers bos)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
