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
    fresh (mon tu we thu fri sat) (sh === Std.list Fun.id [ mon; tu; we; thu; fri; sat ])
  ;;
end

module Plan = struct
  type t = (Lesson.id * Teacher.id) list
end
