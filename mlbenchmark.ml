open Apron
open Mpqf

type oct_type =
  | PX
  | MX
  | PXPY
  | PXMY
  | MXPY
  | MXMY

type var = string

type myoct =
  {
    x : int;
    y : int;
    bound : float;
    ty : oct_type;
  }

let create_oct x y d ty =
  { x=x; y=y; bound=d; ty=ty }

let flip_constraint o =
  match o.ty with
  | PX -> { o with ty = MX; bound = -.(o.bound) }
  | MX -> {o with ty=PX; bound = -.(o.bound) }
  | PXPY -> {o with ty=MXMY; bound = -.(o.bound) }
  | PXMY -> {o with ty=MXPY; bound = -.(o.bound) }
  | MXPY -> {o with ty=PXMY; bound = -.(o.bound) }
  | MXMY -> {o with ty=PXPY; bound = -.(o.bound) }


let oct_type_of_int n =
  match n with
  | 0 -> PX
  | 1 -> MX
  | 2 -> PXPY
  | 3 -> PXMY
  | 4 -> MXPY
  | 5 -> MXMY
  | _ -> assert false
    
let oct_to_string o =
  match o.ty with
  | PX -> Printf.sprintf "x%d <= %f" o.x o.bound
  | MX -> Printf.sprintf "-x%d <= %f" o.x o.bound
  | PXPY -> Printf.sprintf "x%d + x%d <= %f" o.x o.y o.bound
  | PXMY -> Printf.sprintf "x%d - x%d <= %f" o.x o.y o.bound
  | MXPY -> Printf.sprintf "-x%d + x%d <= %f" o.x o.y o.bound
  | MXMY -> Printf.sprintf "-x%d - x%d <= %f" o.x o.y o.bound

let random_int_excluding numvars i =
  let rec _f () =
    let newr = Random.int numvars in
    match newr=i with
    | true -> _f ()
    | false -> newr
  in
  _f ()


(* Creates a constraint with origin as a guaranteed solution *)
let create_constraint numvars =
  let xi = Random.int numvars in
  let yi = random_int_excluding numvars xi in
  let b = float_of_int (10 - (Random.int 20)) in 
  let octtype = Random.int 5 |> oct_type_of_int in
  let oct =
    let _o = create_oct xi yi b octtype in
    if (b < 0.0) then
      flip_constraint _o
    else
      _o
  in
  oct

let random_oct dim numc =
  let rec _random num =
    match num with
    | 0 -> []
    | _ as n -> (create_constraint dim):: (_random (n-1))
  in
  _random numc 

let create_env numc =
  let rec _create_vars numc =
    match numc with
    | 0 -> [(Var.of_string "x0")]
    | _ as n ->
      let v =  Printf.sprintf "x%d" n |> Var.of_string in
      v::(_create_vars (n-1))
  in
  Environment.make (Array.of_list (_create_vars numc)) [||]

(* SYNTAX PARSE ERROR IN THIS ONE *)
(* let test_linexpr man dim numc =
 *   let env = create_env dim in
 *   let o = random_oct dim numc in
 *   let lincons = Parser.lincons1_of_lstring env (List.map oct_to_string o) in
 *   let oct = Abstract1.of_lincons_array man env lincons in
 *   let newo = random_oct dim 10 in
 *   (\* let t = List.fold_left (fun str o -> str ^ ";" ^ (oct_to_string o)) "" newo in *\)
 *   let newlincons = Array.of_list ( List.map (fun o -> oct_to_string o |> Parser.linexpr1_of_string env) newo) in
 *   (\* let newlincons = Parser.linexpr1_of_string env t in *\)
 *   let vars = fst (Environment.vars env) in
 *   let t1 = Unix.gettimeofday () in
 *   let newo = Abstract1.assign_linexpr_array man oct vars newlincons None in
 *   let t2 = Unix.gettimeofday () in
 *   let satmsg =
 *     if (Abstract1.is_top man newo) then
 *       "FINAL_UNSAT"
 *     else
 *       "FINAL_SAT"
 *   in
 *   Printf.printf "Dimension: %d Num new constraints: %d Time: %f %s\n" dim numc (t2 -. t1) satmsg;
 *   t2 -. t1 *)


let print_time dim numc time satmsg =
  Printf.printf "Dimension: %d Num new constraints: %d Time: %f %s\n" dim numc time satmsg;
  flush stdout

let satmsg man abs =
  if (Abstract1.is_top man abs) then
    "FINAL_UNSAT"
  else
    "FINAL_SAT"

let test_init man dim numc =
  let env = create_env dim in
  let o = random_oct dim numc in
  let lincons = Parser.lincons1_of_lstring env (List.map oct_to_string o) in
  let t1 = Unix.gettimeofday () in
  let oct = Abstract1.of_lincons_array man env lincons in
  let t2 = Unix.gettimeofday () in

  let time = t2 -. t1 in
  print_time dim numc time (satmsg man oct);
  time



let test_join man dim numc = 
  let env = create_env dim in
  let o = random_oct dim numc in
  let lincons = Parser.lincons1_of_lstring env (List.map oct_to_string o) in
  let oct = Abstract1.of_lincons_array man env lincons in
  let newo = random_oct dim 10 in
  let newlincons = Parser.lincons1_of_lstring env (List.map oct_to_string newo) in
  let oct2 = Abstract1.of_lincons_array man env newlincons in

  let t1 = Unix.gettimeofday () in
  let newo = Abstract1.join man oct oct2 in
  let t2 = Unix.gettimeofday () in

  let time = t2 -. t1 in
  print_time dim numc time (satmsg man newo);
  time


 
let test_meet man dim numc =
  let env = create_env dim in
  let o = random_oct dim numc in
  let lincons = Parser.lincons1_of_lstring env (List.map oct_to_string o) in
  let oct = Abstract1.of_lincons_array man env lincons in
  let newo = random_oct dim 10 in
  let newlincons = Parser.lincons1_of_lstring env (List.map oct_to_string newo) in

  let t1 = Unix.gettimeofday () in
  let newo = Abstract1.meet_lincons_array man oct newlincons in
  let t2 = Unix.gettimeofday () in

  let time = t2 -. t1 in
  print_time dim numc time (satmsg man newo);
  time



let test_init_opt = ref false
let test_join_opt = ref false
let test_meet_opt = ref false

let _ =

  let spec =
    [("-init", Arg.Set test_init_opt, "Test octagon initialisation");
     ("-join", Arg.Set test_join_opt, "Test octagon join");
     ("-meet", Arg.Set test_meet_opt, "Test octagon meet")]
  in
  (* Build a list of numbers from start to stop 
     Jump is a function int -> int  *)
  let rec _build_nums start jump stop =
    match (start > stop) with
    | true -> []
    | false -> start::(_build_nums (jump start) jump stop)
  in
        
  let iter f n =
    let rec _iter i = 
    match i with
    | 0 -> 0.0
    | _ as j ->
      let s = f () in
      s +. (_iter (j-1))
    in
    _iter n
  in

  let man = Oct.manager_alloc () in
  let numreps = 10 in

  let run_experiment test_func = 
    let dims = _build_nums 5 (fun i -> i + 10) 80 in
    List.iter
      (fun d ->
         let numcs = _build_nums 10 (fun i -> i + 10) (2*d) in
         List.iter
           (fun numc ->
              let f () = test_func man d numc in
              Printf.printf "-----------------------------------------------------------\n"; flush stdout;
              let sum = iter f numreps in
              Printf.printf "SUM: %f AVG: %f\n" sum (sum /. (float_of_int numreps)); flush stdout;
              Printf.printf "-----------------------------------------------------------\n"; flush stdout
           ) numcs) dims
  in
  Arg.parse spec print_endline "Hello";
  if (!test_init_opt) then
    begin
      Printf.printf "Running octagon init microbenchmarks\n"; flush stdout;
      run_experiment test_init
    end;
  if (!test_join_opt) then
    begin
      Printf.printf "Running octagon join microbenchmarks\n"; flush stdout;
      run_experiment test_join
    end;
  if (!test_meet_opt) then
    begin
      Printf.printf "Running octagon meet microbenchmarks\n"; flush stdout;
      run_experiment test_meet
    end
  
      
  
