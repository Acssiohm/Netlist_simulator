open Netlist_ast
open Graph

exception Combinational_cycle
let read_arg a = 
  match a with 
    | Avar x -> [x]
    | Aconst x -> []

let read_exp ( (_,exp) : Netlist_ast.equation) : Netlist_ast.ident list = 
  match exp with
  | Erom (_,_,a) | Eram (_,_,a,_,_,_)| Enot a  | Eslice (_,_,a)  | Eselect (_, a) | Earg a -> read_arg a
  | Ereg _ -> [] 
  | Econcat (a,b) | Ebinop (_, a, b) -> read_arg a @ read_arg b
  | Emux (a,b,c) -> read_arg a @ read_arg b @ read_arg c

let schedule p = 
  let g = mk_graph() in
  List.iter (add_node g) p.p_inputs;
  List.iter (add_node g) (List.map (fun (x,_) -> x) p.p_eqs);
  List.iter (fun (id,exp) -> List.iter (add_edge g id) (read_exp (id, exp))) p.p_eqs;
  let rec combine_eqs (l : Netlist_ast.ident list) : Netlist_ast.equation list = 
    match l with
      | [] -> []
      | id::q -> (try [List.find (fun (id', _) -> id = id') p.p_eqs] with |Not_found -> [])@(combine_eqs q)     
  in
  try
    { p_eqs = combine_eqs (List.rev (topological g));
      p_inputs = p.p_inputs;
      p_outputs = p.p_outputs;
      p_vars = p.p_vars }
  with | Cycle -> raise Combinational_cycle


