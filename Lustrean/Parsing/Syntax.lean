import Lean

declare_syntax_cat lustre_node
declare_syntax_cat lustre_type
declare_syntax_cat lustre_expr
declare_syntax_cat lustre_node_decl
declare_syntax_cat lustre_binding

syntax (name := lustre_command) "lustre " lustre_node* : command
syntax "node " ident "(" lustre_binding,* ")" (" = " (ident),+)?
  " where" (lustre_node_decl)* : lustre_node

syntax ident " : " lustre_type : lustre_binding
syntax ident (" : " lustre_type)? " = " lustre_expr : lustre_node_decl
syntax ident : lustre_type
syntax num : lustre_expr
syntax "-" lustre_expr : lustre_expr
syntax:5 lustre_expr:5 " → " lustre_expr:6 : lustre_expr
syntax:10 lustre_expr:10 " + " lustre_expr:11 : lustre_expr
syntax:10 lustre_expr:10 " - " lustre_expr:11 : lustre_expr
syntax:20 lustre_expr:20 " * " lustre_expr:21 : lustre_expr
syntax:50 " pre " lustre_expr:50 : lustre_expr
syntax ident : lustre_expr
