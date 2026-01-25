open Netlist_ast

let print_only = ref false
let number_steps = ref (-1)
let delay = ref (0)
let quiet = ref( false )
let print_address = ref (-1)
let time_address = ref (-1)

let rec value_of_int t n =
  match t with
    | TBit -> if n <> 0 && n <> 1 then failwith "Wrong input" else VBit (n = 1)
    | TBitArray k -> if n > (1 lsl k) - 1 || n < - ( 1 lsl (k-1))  then failwith ("Wrong input") else
      if n < 0 then (value_of_int t ( (1 lsl k) + n )) else 
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
    let n = Array.length a in 
    assert (n <= Sys.int_size);
    let mask = if a.(n-1) then lnot ( (1 lsl n) - 1 ) else 0 in 
    let s = Array.fold_left (fun x y -> y^x ) "" (Array.map (fun b -> if b then "1" else "0") a) in
    print_int(x lor mask) ; print_string "  u" ;print_int x; print_string (" (0b"^s^")")
  
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

let read_value t =
  let res = value_of_int t (read_number ()) in
  print_value res;
  print_newline ();
  res

let print_module ram = 
  if !print_address >= 0 then 
    Hashtbl.iter (fun _ r -> if int_of_value(r.(!print_address)) <> 0 then 
      (print_int (int_of_value r.(!print_address + 1)); print_newline ();
      r.(!print_address) <- (VBitArray (Array.make 32 false)))) ram

let varray_of_int i n = 
  let r = ref i in 
  VBitArray (Array.init n (fun _ -> 
    if !r mod 2 = 0 then (r:=!r/2;false)
    else (r:=!r/2;true)))

let time_module ram =
  if !time_address >= 0 then 
    Hashtbl.iter (fun _ r -> 
      r.(!time_address) <- varray_of_int (int_of_float (Unix.time ())) 32) ram

let simulator program number_steps = 
  let vars = Hashtbl.create (List.length program.p_inputs) in
  let ram =  Hashtbl.create 5 in 
  let rom =  Hashtbl.create 3 in
  (*let mem_map = ref [] in *)
  (* Create the RAMs *)
  List.iter (fun (x,e) -> match e with 
  | Eram (addr,word,_,_,_,_) -> 
    (*print_endline ("Set some adresses of the RAM "^x^" as output :");
    (try 
    while true do
      let n = read_number() in
      assert (n mod 4 = 0);
      mem_map := (n/4, x)::!mem_map
    done
    with | Failure s -> if s = "int_of_string" then () else failwith s );*)
    Hashtbl.replace ram x (Array.init (1 lsl addr) (fun _ -> value_of_type (TBitArray word) ))
  | _ -> () 
  ) program.p_eqs;
  (* Create and initialize ROMs with user inputs *)
  List.iter (fun (x,e) -> match e with 
  | Erom (addr,word,_) -> begin 
    Hashtbl.replace rom x (Array.init (1 lsl addr) (fun _ -> VBitArray (Array.make word false)));
    print_endline ("Enter values for the ROM '"^x^"' (or enter to end) :");
    print_endline ("Adress size is "^(string_of_int addr)^". Word size is "^(string_of_int word));
    print_string "Get from file (or enter to put manually):";
    let filename = read_line() in 
    let ch =  if filename = "" then Stdlib.stdin else Stdlib.open_in filename in 
    let finish = ref false in
    let i = ref 0 in 
    while not !finish do
      try
        if filename = "" then Printf.printf ">>>%!"; 
        let e = strip (Stdlib.input_line ch) in
        let s, is_address = if e <> "" && e.[0] = '.' then (String.sub e 1 ((String.length e)  - 1), true) else (e, false) in
        let n = int_of_string s in
        if is_address then (
          assert ( n mod 4 = 0); 
          i := n / 4 )
        else 
          (
          let v =  value_of_int (TBitArray word) n in
          (Hashtbl.find rom x).(!i) <- v;
          i := !i+1
        )
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
  let last_time = ref (Sys.time()) in
  while !i <> number_steps do
    if (Sys.time() -. !last_time) *. 1000.0 >= float_of_int !delay then 
      (time_module ram;
      last_time := Sys.time();
      if not !quiet then (print_string "Step "; print_int (!i+1); print_string " :\n");
      (* Getting the inputs *)
      (if program.p_inputs = [] then () else
      List.iter (fun input -> print_string (input^" ? "); Hashtbl.replace vars input ( read_value (Env.find input program.p_vars))) program.p_inputs);
      List.iter exec_eq program.p_eqs;
      (* Writing the outputs *)
      if not !quiet then List.iter (fun output -> print_string ("=> "^output^" = "); print_value (Hashtbl.find vars output); print_newline () ) program.p_outputs;
      (*List.iter (fun (addr, x) -> print_string ("--> "); print_value (Hashtbl.find ram x).(addr); print_newline () ) (List.rev !mem_map) ;*)
      print_module ram;
      update_mem();
      i := !i+1)
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
    ["-n", Arg.Set_int number_steps, "Number of steps to simulate";
     "-d", Arg.Set_int delay, "Clock period";
     "-q", Arg.Set quiet, "Quiet mode";
     "--print", Arg.Set_int print_address, "Définition d'un emplacement de ram pour le périphérique de sortie textuel";
     "--time", Arg.Set_int time_address, "Définition d'un emplacement de ram pour le périphérique de sortie textuel"]
    compile
    ""
;;

main ()
