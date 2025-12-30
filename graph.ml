exception Cycle
type mark = NotVisited | InProgress | Visited

type 'a graph =
    { mutable g_nodes : 'a node list }
and 'a node = {
  n_label : 'a;
  mutable n_mark : mark;
  mutable n_link_to : 'a node list;
  mutable n_linked_by : 'a node list;
}

let mk_graph () = { g_nodes = [] }

let add_node g x =
  let n = { n_label = x; n_mark = NotVisited; n_link_to = []; n_linked_by = [] } in
  g.g_nodes <- n :: g.g_nodes

let node_of_label g x =
  List.find (fun n -> n.n_label = x) g.g_nodes

let add_edge g id1 id2 =
  try
    let n1 = node_of_label g id1 in
    let n2 = node_of_label g id2 in
    n1.n_link_to   <- n2 :: n1.n_link_to;
    n2.n_linked_by <- n1 :: n2.n_linked_by
  with Not_found -> Format.eprintf "Tried to add an edge between non-existing nodes"; raise Not_found

let clear_marks g =
  List.iter (fun n -> n.n_mark <- NotVisited) g.g_nodes

let find_roots g =
  List.filter (fun n -> n.n_linked_by = []) g.g_nodes

let has_cycle g = 
  clear_marks g ;
  let rec explore_from (s : 'a node) : bool =
    match s.n_mark with  
      | InProgress -> true
      | Visited -> false 
      | NotVisited -> begin 
        s.n_mark <- InProgress ;
        let res = List.exists explore_from s.n_link_to in
        s.n_mark <- Visited;
        res 
      end
  in
  List.exists explore_from g.g_nodes
 
let topological g = 
  let rec explore_from l s =
    match s.n_mark with
      | Visited -> l
      | NotVisited -> (s.n_mark <-Visited; s.n_label::(List.fold_left explore_from l s.n_link_to))
      | InProgress -> assert false
    in
  if has_cycle g then 
    raise Cycle 
  else begin
    clear_marks g;
    List.fold_left explore_from [] (find_roots g)
  end 
