let log fmt =
  if true
  then Format.kasprintf print_endline fmt
  else Format.ifprintf Format.std_formatter fmt
;;

type group_id = int
type teacher_id = string

module Lesson = struct
  type id = string
  type t = id
end

module Constraint = struct
  type t =
    | Bad_lesson of int
    | Bad_day of int
end

(* Teacher's lesson *)
module Para = struct
  [%%ocanren_inject
    type nonrec ground =
      | Window
      | Lesson of GT.int * GT.string * GT.string
    [@@deriving gt ~options:{ gmap; show }]]

  let blank : injected = OCanren.( !! ) Window

  let lesson ~group_id ~teacher_id ~course_id =
    let open OCanren in
    lesson !!group_id !!teacher_id !!course_id
  ;;
end

module Stud_para = struct
  [%%ocanren_inject
    type nonrec ground =
      | Elective of GT.string * (GT.string * GT.string) OCanren.Std.List.ground
      | Default of Para.ground
    [@@deriving gt ~options:{ gmap; show }]]

  let _ = elective
  (*
     type reified =
     (GT.string, (GT.string * GT.string) OCanren.Std.List.ground, Para.logic) t
     OCanren.logic

     let smart_reify : OCanren.Reifier.t (injected,reified) = *)

  let elective title xs : injected =
    let open OCanren in
    OCanren.inj (Elective (!!title, Std.list (fun (a, b) -> Std.pair !!a !!b) xs))
  ;;

  let blank : injected = default Para.blank
end

let conj_map ~f xs =
  let open OCanren in
  List.fold_left (fun acc x -> acc &&& f x) success xs
;;

let condeep_map ~f xs =
  let open OCanren in
  List.fold_left (fun acc x -> condeep [ acc; f x ]) failure xs
;;

module Schedule = struct
  open OCanren

  type 'para injected = 'para Std.List.injected Std.List.injected
  type 'para logic = 'para Std.List.logic Std.List.logic
  type 'para reifed = 'para Std.List.ground Std.List.ground

  let reify r : (_ injected, _ reifed) Reifier.t = Std.List.prj_exn (Std.List.prj_exn r)

  let is sched i j para =
    let _ : _ injected = sched in
    let open OCanren in
    fresh
      (m tu w th fr sa day para1 para2 para3 para4)
      (sched === Std.list Fun.id [ m; tu; w; th; fr; sa ])
      (match i with
       | 0 -> day === m
       | 1 -> day === tu
       | 2 -> day === w
       | 3 -> day === th
       | 4 -> day === fr
       | 5 -> day === sa
       | _ -> assert false)
      (day === Std.list Fun.id [ para1; para2; para3; para4 ])
      (match j with
       | 0 -> para === para1
       | 1 -> para === para2
       | 2 -> para === para3
       | 3 -> para === para4
       | _ -> assert false)
  ;;

  let set_signlo sched i j para = is sched i j para
  let blank_day = Std.list Fun.id [ Para.blank; Para.blank; Para.blank; Para.blank ]

  let bad_dayo day : _ -> _ injected -> goal =
    fun blank_para sched ->
    fresh
      (m tu w th fr sa blank_day)
      (sched === Std.list Fun.id [ m; tu; w; th; fr; sa ])
      (blank_day === Std.list Fun.id [ blank_para; blank_para; blank_para; blank_para ])
      (match day with
       | 0 -> blank_day === m
       | 1 -> blank_day === tu
       | 2 -> blank_day === w
       | 3 -> blank_day === th
       | 4 -> blank_day === fr
       | 5 -> blank_day === sa
       | _ -> assert false)
  ;;
end

module Stud_schedule = struct
  type injected = Stud_para.injected Schedule.injected
end

let init_empty_schedule : _ Schedule.injected -> OCanren.goal =
  fun sh ->
  let open OCanren in
  let wrap day = fresh (l1 l2 l3 l4) (day === Std.list Fun.id [ l1; l2; l3; l4 ]) in
  fresh
    (mon tu we thu fri sat)
    (sh === Std.list Fun.id [ mon; tu; we; thu; fri; sat ])
    (wrap mon)
    (wrap tu)
    (wrap we)
    (wrap thu)
    (wrap fri)
    (wrap sat)
;;

(* let schedule_without_windows : Para.injected Schedule.injected -> OCanren.goal =
   fun sh ->
   let open OCanren in
   let wrap ?(hack = false) day =
   fresh
   (l1 l2 l3 l4)
   (day === Std.list Fun.id [ l1; l2; l3; l4 ])
   (* (Std.triple l1 l2 l3
   =/= Std.triple !!(Para.Lesson (__, __, __)) Para.blank !!(Para.Lesson (__, __, __))
   ) *)
   (if hack
   then
   Std.triple l2 l3 l4
   =/= Std.triple
   !!(Para.Lesson (__, __, __))
   Para.blank
   !!(Para.Lesson (__, __, __))
   else success)
   in
   fresh
   (mon tu we thu fri sat)
   (sh === Std.list Fun.id [ mon; tu; we; thu; fri; sat ])
   (wrap mon)
   (wrap tu)
   (wrap ~hack:true we)
   (wrap ~hack:true thu)
   (wrap fri)
   (wrap ~hack:true sat)
   ;; *)

module Plan_item = struct
  type 'gid cstrnt =
    | Dont_ovelap of 'gid
    | Hardcode of int * int

  type 'gid t =
    | Normal of
        { group_id : group_id
        ; lesson_id : Lesson.id
        ; teacher_id : teacher_id
        ; constraints : 'gid cstrnt list
        }
    | Elective of
        { title : string
        ; group_id : group_id
        ; electives : (teacher_id * Lesson.id) list
        }
end

module Teacher = struct
  type id = string

  type t =
    { id : id
    ; constraints : Constraint.t list
    ; arr : bool array array
    ; indexes : (int * int) list
    }

  let day_count = 6
  let pair_per_day = 4

  let arr_allow_anyting () =
    Array.init day_count (fun _ -> Array.init pair_per_day (fun _ -> true))
  ;;

  let foreach_matrix f arr =
    for i = 0 to day_count - 1 do
      for j = 0 to pair_per_day - 1 do
        f i j arr.(i).(j)
      done
    done
  ;;

  let fold_matrix f acc arr =
    let rec loopj i j acc =
      if j >= pair_per_day
      then acc
      else if arr.(i).(j)
      then loopj i (1 + j) (f i j acc)
      else loopj i (1 + j) acc
    in
    let rec loopi i acc =
      if i >= day_count
      then acc
      else (
        let acc = loopj i 0 acc in
        loopi (1 + i) acc)
    in
    loopi 0 acc
  ;;

  let decribe_matrix title m =
    let choices = fold_matrix (fun _ _ acc -> acc + 1) 0 m in
    if choices <= 0
    then (
      Printf.printf " Teacher %S has NO choices\n" title;
      false)
    else (
      Printf.printf "There are %d choices for teacher %S\n%!" choices title;
      true)
  ;;

  let indexes_of_matrix arr =
    let indexes = ref [] in
    foreach_matrix (fun i j flg -> if flg then indexes := (i, j) :: !indexes) arr;
    !indexes
  ;;

  let create id constraints =
    let arr = arr_allow_anyting () in
    ListLabels.iter constraints ~f:(function
      | Constraint.Bad_day n ->
        for i = 0 to pair_per_day - 1 do
          arr.(n).(i) <- false
        done
      | Bad_lesson n ->
        for i = 0 to day_count - 1 do
          arr.(i).(n) <- false
        done);
    let indexes = indexes_of_matrix arr in
    let () = if constraints = [] then assert (List.length indexes = 6 * 4) in
    assert (decribe_matrix id arr);
    { id; constraints; arr; indexes }
  ;;

  type schedule_injected = Para.injected Schedule.injected

  let init_schedule t : schedule_injected -> OCanren.goal =
    fun sh ->
    let open OCanren in
    let wrap day arr =
      fresh
        (l1 l2 l3 l4)
        (day === Std.list Fun.id [ l1; l2; l3; l4 ])
        (if arr.(0) then success else l1 === Para.blank)
        (if arr.(1) then success else l2 === Para.blank)
        (if arr.(2) then success else l3 === Para.blank)
        (if arr.(3) then success else l4 === Para.blank)
    in
    fresh
      (mon tu we thu fri sat)
      (sh === Std.list Fun.id [ mon; tu; we; thu; fri; sat ])
      (wrap mon t.arr.(0))
      (wrap tu t.arr.(1))
      (wrap we t.arr.(2))
      (wrap thu t.arr.(3))
      (wrap fri t.arr.(4))
      (wrap sat t.arr.(5))
  ;;

  let arr_foldi f acc arr =
    let rec helper acc i =
      if i >= Array.length arr then acc else helper (f i acc arr.(i)) (1 + i)
    in
    helper acc 0
  ;;

  let apply_para_constraints ~get_group_sched i j cstrnts =
    let _ : _ -> Stud_para.injected Schedule.injected = get_group_sched in
    let open OCanren in
    List.fold_left
      (fun acc -> function
        | Plan_item.Dont_ovelap other_gid ->
          acc &&&& Schedule.set_signlo (get_group_sched other_gid) i j Stud_para.blank
        | Hardcode _ ->
          (* We don't apply the constraint because it will be applied elsewhere *)
          acc)
      success
      cstrnts
  ;;

  let shrink_placement t constraints =
    match
      List.find_map
        (function
          | Plan_item.Hardcode (a, b) -> Some (a, b)
          | _ -> None)
        constraints
    with
    | Some pos -> List.filter (( = ) pos) t.indexes
    | None ->
      (* TODO: support don't overlap *)
      t.indexes
  ;;

  let placeo ~get_group_sched t teacher_sched group_sched =
    let _ : schedule_injected = teacher_sched in
    let _ : _ -> Stud_para.injected Schedule.injected = get_group_sched in
    function
    | Plan_item.Normal { group_id; teacher_id; lesson_id; constraints } ->
      let para = Para.lesson ~group_id ~teacher_id ~course_id:lesson_id in
      let open OCanren in
      condeep_map (shrink_placement t constraints) ~f:(fun (i, j) ->
        Schedule.is teacher_sched i j para
        &&& Schedule.is group_sched i j (Stud_para.default para)
        &&&& apply_para_constraints ~get_group_sched i j constraints)
    | Elective _ -> assert false
  ;;
end

module Plan = struct
  type t = group_id Plan_item.t list
  type pre_plan = string Plan_item.t list

  type collection =
    { group_of_id : (int, string) Hashtbl.t
    ; id_of_group : (string, int) Hashtbl.t
    ; mutable last_id : int
    }

  let col =
    { group_of_id = Hashtbl.create 100; id_of_group = Hashtbl.create 100; last_id = 1 }
  ;;

  let clear () =
    col.last_id <- 1;
    Hashtbl.clear col.group_of_id;
    Hashtbl.clear col.id_of_group
  ;;

  let group_of_id = Hashtbl.find col.group_of_id

  let register_group g =
    match Hashtbl.find col.id_of_group g with
    | id -> id
    | exception Not_found ->
      let id = col.last_id in
      col.last_id <- 1 + col.last_id;
      Hashtbl.replace col.id_of_group g id;
      Hashtbl.replace col.group_of_id id g;
      id
  ;;

  let make ?(cstrnts = []) ~g ~t lesson_id =
    let group_id = register_group g in
    Plan_item.Normal { group_id; lesson_id; teacher_id = t; constraints = cstrnts }
  ;;

  (** [make_elective title ~g lessons] when lessons is teacher/lesson list *)
  let make_elective title ~g electives =
    assert (electives <> []);
    let group_id = register_group g in
    Plan_item.Elective { title; group_id; electives }
  ;;

  (* Replaces string GIDs to grounp_id type *)
  let of_pre_plan : pre_plan -> t =
    List.map (function
      | Plan_item.Normal { lesson_id; group_id; teacher_id; constraints } ->
        let constraints =
          List.map
            (function
              | Plan_item.Dont_ovelap gname ->
                Plan_item.Dont_ovelap (Hashtbl.find col.id_of_group gname)
              | Hardcode _ as c -> c)
            constraints
        in
        Plan_item.Normal { lesson_id; group_id; teacher_id; constraints }
      | Plan_item.Elective x -> Plan_item.Elective x)
  ;;
end

let synth get_teacher ~get_teacher_sched ~get_group_sched (plan : Plan.t) =
  let _ : _ -> Stud_para.injected Schedule.injected = get_group_sched in
  let open OCanren in
  Stdlib.List.fold_left
    (fun acc -> function
      | Plan_item.Normal { group_id; teacher_id; _ } as item ->
        let group_sched : Stud_para.injected Schedule.injected =
          get_group_sched group_id
        in
        let teacher_sched = get_teacher_sched teacher_id in
        let teacher = get_teacher teacher_id in
        acc &&& Teacher.placeo ~get_group_sched teacher teacher_sched group_sched item
      | Elective { title; group_id; electives } ->
        let joined_arr =
          List.fold_left
            (fun acc (tid, _) ->
              let x = (get_teacher tid).arr in
              if not (Teacher.decribe_matrix tid x) then exit 1;
              Teacher.foreach_matrix (fun i j c -> acc.(i).(j) <- acc.(i).(j) && c) x;
              acc)
            (Teacher.arr_allow_anyting ())
            electives
        in
        let indexes =
          Teacher.indexes_of_matrix joined_arr
          |> List.sort (fun (_, a) (_, b) -> Int.compare a b)
        in
        let () =
          let choices = Teacher.fold_matrix (fun _ _ acc -> acc + 1) 0 joined_arr in
          if choices <= 0
          then failwith "No choices"
          else (
            let __ () =
              Printf.printf "There are %d choices for elective %S\n%!" choices title
            in
            ())
        in
        let group_sched : Stud_para.injected Schedule.injected =
          get_group_sched group_id
        in
        acc
        &&&& ListLabels.fold_left
               ~f:(fun acc (i, j) ->
                 (* Printf.printf "Iterating over %d,%d\n%!" i j; *)
                 condeep
                   [ acc
                   ; conj_map electives ~f:(fun (teacher_id, course_id) ->
                       let teacher_sched = get_teacher_sched teacher_id in
                       Schedule.is
                         teacher_sched
                         i
                         j
                         (Para.lesson ~group_id ~teacher_id ~course_id))
                     &&& Schedule.is group_sched i j (Stud_para.elective title electives)
                   ])
               ~init:failure
               indexes)
    success
    plan
;;
