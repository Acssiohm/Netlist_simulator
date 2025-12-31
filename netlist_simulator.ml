open Netlist_ast

let print_only = ref false
let number_steps = ref (-1)

let value_of_int t n =
  match t with
    | TBit -> if n <> 0 && n <> 1 then failwith "Wrong input" else VBit (n = 1)
    | TBitArray k -> if n < 0 || n >= (1 lsl k) then failwith "Wrong input" else 
      VBitArray (Array.init k (fun i -> ((n lsr i) land 1) = 1 ))

let int_of_bool b = if b then 1 else 0

let int_of_bool_array arr =
  let n = Array.length arr in
  let res = ref 0 in
  for i = 0 to n-1 do
    res := !res lor ((int_of_bool arr.(i)) lsl i) 
  done;
  !res

let int_of_value v =
  match v with
    | VBit b -> int_of_bool b
    | VBitArray arr -> int_of_bool_array arr 



  
let array_of_value v =
  match v with
    | VBit b -> [|b|]
    | VBitArray arr -> arr 


let print_value v =
    let x = int_of_value v in
    let a = array_of_value v in
    let s = Array.fold_left (fun x y -> y^x ) "" (Array.map (fun b -> if b then "1" else "0") a) in
    print_int x; print_string (" (0b"^s^")")
    

  
let value_of_type t =
  match t with
    | TBit -> VBit false
    | TBitArray n -> VBitArray (Array.make n false)

let () =
    assert (value_of_int (TBitArray 4) 0b1101 = VBitArray [|true; false; true; true|])
  
let strip (s : string) : string =
  if s = "" then "" else 
  let spaces = [' '; '\t'] in
  let i = ref 0 in
  while !i < String.length s && List.mem s.[!i] spaces do
    i := !i + 1
  done;
  let j = ref (String.length s - 1) in
  while List.mem s.[!j] spaces && !j >= !i do
    j := !j - 1
  done;
  String.sub s !i (!j - !i + 1)

let () =
  assert (strip "  Bonjour  " = "Bonjour");
  assert (strip " \t Bon  jour  " = "Bon  jour");
  assert (strip "  Bon  jour" = "Bon  jour");
  assert (strip "Bon  jour  " = "Bon  jour");
  assert (strip "    " = "");
  assert (strip "" = "")

let read_number () =
  int_of_string(strip (read_line ()))

let simulator program number_steps = 
  let vars = Hashtbl.create (List.length program.p_inputs) in
  let ram =  Hashtbl.create 5 in 
  let rom =  Hashtbl.create 3 in
  (* Create the RAMs *)
  List.iter (fun (x,e) -> match e with 
  | Eram (addr,word,_,_,_,_) -> Hashtbl.replace ram x (Array.init (1 lsl addr) (fun _ -> value_of_type (TBitArray word) ))
  | _ -> () 
  ) program.p_eqs;
  (* Create and initialize ROMs with user inputs *)
  List.iter (fun (x,e) -> match e with 
  | Erom (addr,word,_) -> begin 
    Hashtbl.replace rom x (Array.init (1 lsl addr) (fun _ -> VBitArray (Array.make word false)));
    print_endline ("Enter values for the ROM '"^x^"' (or enter to end) :");
    print_endline ("Adress size is "^(string_of_int addr)^". Word size is "^(string_of_int word));
    let finish = ref false in
    while not !finish do
      try 
        print_string "Adress ? "; 
        let a = read_number () in
        print_string "Value ? ";
        let v = value_of_int (TBitArray word) (read_number ()) in
        (Hashtbl.find rom x).(a) <- v
      with | Failure s -> if s = "int_of_string" then finish := true else failwith s
    done
  end
  | _ -> () 
  ) program.p_eqs;
  (* Put initial values inside registers *)
  List.iter (fun (x,e) -> match e with 
  | Ereg x' -> Hashtbl.replace vars x (value_of_type (Env.find x program.p_vars)) 
  | _ -> () 
  ) program.p_eqs;
  (* Finds the value of an arg *)
  let eval_arg = function
    | Avar s -> Hashtbl.find vars s
    | Aconst c -> c
  in 
  let update_var = Hashtbl.replace vars in
  let map_value f v =
    match v with
      | VBit b -> VBit (f b)
      | VBitArray ba -> VBitArray (Array.map f ba) 
  in
  let map2_value f v1 v2 =
    match v1, v2 with
      | VBit b1, VBit b2 | VBitArray [|b1|], VBit b2 | VBit b1, VBitArray [|b2|]   -> VBit (f b1 b2)
      | VBitArray ba1, VBitArray ba2 -> VBitArray (Array.map2 f ba1 ba2)
      | _ -> failwith "input sizes don't match"
  in
  (* Execution of one equation *)
  let exec_eq (x,e) =
    match e with
    | Earg a -> update_var x (eval_arg a)
    | Ereg _ -> ()
    | Enot a -> update_var x (map_value (not) (eval_arg a))
    | Ebinop (op,a1,a2) -> begin 
      let f_op = match op with
          | And -> (&&)
          | Nand -> (fun b1 b2 -> not (b1 && b2))
          | Xor -> (<>)
          | Or -> (||)
      in
      update_var x (map2_value f_op (eval_arg a1) (eval_arg a2))
    end
    | Emux (ch, a, b) ->  update_var x 
      (match eval_arg ch with
        | VBit c | VBitArray [|c|] -> if c then eval_arg b else eval_arg a
        | _ -> failwith "input of mux not of size 1")
    | Eram (_,_,read_addr, write_en, write_addr, data) -> begin
      let memory = Hashtbl.find ram x  in
      update_var x memory.(int_of_value (eval_arg read_addr))
      end
    | Erom (_,_,read_addr) -> begin
        let memory = Hashtbl.find rom x in
        update_var x memory.(int_of_value (eval_arg read_addr))
        end
    | Econcat (a1,a2) -> update_var x (VBitArray (Array.append (array_of_value (eval_arg a1)) (array_of_value (eval_arg a2))))
    | Eslice (i1, i2, a) -> update_var x (VBitArray (Array.sub (array_of_value (eval_arg a)) i1 (i2-i1+1)))
    | Eselect (i,a) -> update_var x (VBit (array_of_value (eval_arg a)).(i) )
  in
  (* Update RAM and registers *)
  let update_mem () = List.iter (
    fun (x,e) -> match e with
    | Eram (_,_,_,write_en, write_addr, data) -> begin let memory = Hashtbl.find ram x  in
    (match eval_arg write_en with
      | VBit en | VBitArray [|en|] -> if en then memory.(int_of_value (eval_arg write_addr)) <- (eval_arg data)
      | _ -> failwith "write enable not of size 1") end
    | Ereg x' -> update_var x (Hashtbl.find vars x')
    | _ -> ()
  ) program.p_eqs 
  in
  let i = ref 0 in
  while !i <> number_steps do
    print_string "Step "; print_int (!i+1); print_string " :\n" ;
    (* Getting the inputs *)
    List.iter (fun input -> print_string (input^" ? "); Hashtbl.replace vars input ( value_of_int (Env.find input program.p_vars) (read_number ()))) program.p_inputs;
    List.iter exec_eq program.p_eqs;
    (* Writing the outputs *)
    List.iter (fun output -> print_string ("=> "^output^" = "); print_value (Hashtbl.find vars output); print_newline () ) program.p_outputs;
    update_mem();
    i := !i+1
  done

let compile filename =
  try
    let p = Netlist.read_file filename in
    begin try
        let p = Scheduler.schedule p in
        simulator p !number_steps
      with
        | Scheduler.Combinational_cycle ->
            Format.eprintf "The netlist has a combinatory cycle.@.";
    end;
  with
    | Netlist.Parse_error s -> Format.eprintf "An error accurred: %s@." s; exit 2

let main () =
  Arg.parse
    ["-n", Arg.Set_int number_steps, "Number of steps to simulate"]
    compile
    ""
;;

main ()
