let log fmt =
  if true
  then Format.kasprintf print_endline fmt
  else Format.ifprintf Format.std_formatter fmt
;;

type group_id = int

module Lesson = struct
  type id = string
  type t = id
end

module Constraint = struct
  type t =
    | Bad_lesson of int
    | Bad_day of int
end

module Para = struct
  [%%ocanren_inject
    type nonrec ground =
      | Window
      | Lesson of GT.int * GT.string * GT.string
    [@@deriving gt ~options:{ gmap }]]

  let blank : injected = OCanren.( !! ) Window

  let lesson ~group_id ~teacher_id ~course_id =
    let open OCanren in
    lesson !!group_id !!teacher_id !!course_id
  ;;
end

module Schedule = struct
  open OCanren

  type injected = Para.injected Std.List.injected Std.List.injected
  type logic = Para.logic Std.List.logic Std.List.logic
  type reifed = Para.logic Std.List.ground Std.List.ground

  let reify : (injected, reifed) Reifier.t =
    Std.List.prj_exn (Std.List.prj_exn Para.reify)
  ;;

  let is sched i j para =
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
end

let init_empty_schedule : Schedule.injected -> OCanren.goal =
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

module Teacher = struct
  type id = string

  type t =
    { id : id
    ; constraints : Constraint.t list
    ; arr : bool array array
    }

  let create id constraints =
    let arr = Array.init 6 (fun _ -> Array.init 4 (fun _ -> true)) in
    constraints
    |> List.iter (function
      | Constraint.Bad_day n ->
        for i = 0 to 4 - 1 do
          arr.(n).(i) <- false
        done
      | Bad_lesson n ->
        for i = 0 to 6 - 1 do
          arr.(i).(n) <- false
        done);
    { id; constraints; arr }
  ;;

  let init_schedule t : Schedule.injected -> OCanren.goal =
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

  let placeo t teacher_sched group_sched v =
    let _ : Schedule.injected = teacher_sched in
    let _ : Schedule.injected = group_sched in
    let open OCanren in
    arr_foldi
      (fun i acc ->
        arr_foldi
          (fun j acc _ ->
            if t.arr.(i).(j)
            then
              conde
                [ acc; Schedule.is teacher_sched i j v &&& Schedule.is group_sched i j v ]
            else acc)
          acc)
      OCanren.failure
      t.arr
  ;;
end

module Plan = struct
  type t = (group_id * Lesson.id * Teacher.id) list

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

  let make ~g ~t lesson =
    let gid =
      match Hashtbl.find col.id_of_group g with
      | id -> id
      | exception Not_found ->
        let id = col.last_id in
        col.last_id <- 1 + col.last_id;
        Hashtbl.replace col.id_of_group g id;
        Hashtbl.replace col.group_of_id id g;
        id
    in
    gid, lesson, t
  ;;
end

let synth get_teacher ~get_teacher_sched ~get_group_sched (plan : Plan.t) =
  let open OCanren in
  Stdlib.List.fold_left
    (fun acc (group_id, course_id, teacher_id) ->
      let teacher_sched = get_teacher_sched teacher_id in
      let group_sched = get_group_sched group_id in
      let teacher = get_teacher teacher_id in
      acc
      &&& Teacher.placeo
            teacher
            teacher_sched
            group_sched
            (Para.lesson ~group_id ~teacher_id ~course_id))
    success
    plan
;;
