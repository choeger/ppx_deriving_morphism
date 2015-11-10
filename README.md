# ppx_deriving_morphism
Deriving Morphisms for arbitrary OCaml data structures 

This package provides a plugin for ppx_deriving that generates morphisms in the style of the ast_mapper in the ocaml source tree for arbitrary data structures (with a clear focus on syntax trees).

== Usage ==


== Limitations ==

At this early stage, the implementation has some limitations:

* Currently, there is no way to derive a signature for a folder or a mapper
* The fact that there needs to be a name of the morphism-records means that only one folder and mapper can be derived for each module
* Only constructors in the recursive group are considered by the automatically generated folder and mapper
