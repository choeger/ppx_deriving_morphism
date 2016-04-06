# ppx_deriving_morphism
Deriving Morphisms for arbitrary OCaml data structures 

This package provides a plugin for ppx_deriving that generates morphisms in the style of [the ast_mapper in the ocaml source tree](https://github.com/ocaml/ocaml/blob/trunk/parsing/ast_mapper.ml) for arbitrary data structures (with a clear focus on syntax trees).

## Usage
Consider a typical small functional language:
```ocaml
    type expr =
      | Abs of unit binding
      | App of app
      | Let of expr binding
      | Var of string
      | Int of int
    and app = {
      lhs: expr;
      arg: expr;}
    and 'a binding = {
      var: string;
      rhs: 'a;
      bdy: expr;}[@@deriving (folder, mapper)]
```

The last line generates ```folder``` and ```mapper``` routines:

```ocaml
    type 'b folder =
      {
      fold_binding: 'a . ('a -> 'b -> 'b) -> ('b,'a binding) fold_routine;
      fold_app: ('b,app) fold_routine;
      fold_expr: ('b,expr) fold_routine;
      on_expr: 'b expr_folder;}
    and ('a,'b) fold_routine = 'a folder -> 'b -> 'a -> 'a
    and 'b expr_folder =
      {
      fold_Abs: ('b,unit binding) fold_routine;
      fold_App: ('b,app) fold_routine;
      fold_Let: ('b,expr binding) fold_routine;
      fold_Var: ('b,string) fold_routine;
      fold_Int: ('b,int) fold_routine;}
    type mapper =
      {
      map_binding: 'a . ('a -> 'a) -> ('a binding,'a binding) map_routine;
      map_app: (app,app) map_routine;
      map_expr: (expr,expr) map_routine;
      on_expr: expr_mapper;}
    and ('a,'b) map_routine = mapper -> 'a -> 'b
    and expr_mapper =
      {
      map_Abs: (unit binding,expr) map_routine;
      map_App: (app,expr) map_routine;
      map_Let: (expr binding,expr) map_routine;
      map_Var: (string,expr) map_routine;
      map_Int: (int,expr) map_routine;}
```

There is also an automatically generated ```identity_folder``` and ```identity_mapper``` which only traverse the structure.

To implement a typical operation, one can now "extend" these default implementations:

```ocaml
  let fv_folder = { identity_folder with
                    fold_binding =
                      (fun f self {var;rhs;bdy} ->
                         self.fold_expr self bdy %>
                         filter var %>
                         f rhs ) ;
                    on_expr = { identity_folder.on_expr with fold_Var = (fun self -> cons) }
                  }
```

Obviously the benefit is bigger for more specialized operations (free variables is a good example, since it is not affected by many constructors in the language. Another example would be capture-avoiding substitution (for a ```mapper```).

## Limitations

At this early stage, the implementation has some limitations:

* Currently, there is no way to derive a signature for a folder or a mapper
* The fact that there needs to be a name of the morphism-records means that only one folder and mapper can be derived for each module
* Only constructors in the recursive group are considered by the automatically generated folder and mapper

