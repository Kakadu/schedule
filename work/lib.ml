type group_id = int

module Lesson = struct
  type id = int

  type t =
    { id : id
    ; desc : string
    }
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
      | Lesson of GT.int * GT.int
    [@@deriving gt ~options:{ gmap }]]

  let blank : injected = OCanren.( !! ) Window
end

module Schedule = struct
  open OCanren

  type injected = Para.injected Std.List.injected Std.List.injected
end

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
    arr_foldi (fun i acc -> arr_foldi (fun j acc _ -> acc) acc) OCanren.failure t.arr
  ;;
end

module Plan = struct
  type t = (group_id * Lesson.id * Teacher.id) list
end

let synth get_teacher_sched get_group_sched plan =
  let open OCanren in
  List.fold_left (fun acc (group_sched, les_id, tchr_id) -> acc) success plan
;;
