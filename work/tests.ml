open OCanren

let%expect_test "" =
  let open Tester in
  let constraint1 q = fresh (u v) (q =/= Std.triple u !!1 v) (u =/= !!1) (v =/= !!1) in
  let run eta =
    run_r
      [%reify: (GT.int, GT.int, GT.int) Std.Triple.t]
      ([%show: (GT.int logic, GT.int logic, GT.int logic) Std.Triple.logic] ())
      eta
  in
  [%tester run 1 (fun q -> constraint1 q)];
  [%expect "
    fun q -> constraint1 q, 1 answer {
    q=_.10 [=/= (_.11 [=/= 1], 1, _.12 [=/= 1])];
    }"];
  [%tester run 1 (fun q -> constraint1 q &&& (q === Std.triple !!1 !!2 !!1))];
  [%expect "
    fun q -> (constraint1 q) &&& (q === (Std.triple (!! 1) (!! 2) (!! 1))), 1 answer {
    q=(1, 2, 1);
    }"];
  [%tester run 1 (fun q -> constraint1 q &&& (q === Std.triple !!2 !!1 !!2))];
  [%expect "
    fun q -> (constraint1 q) &&& (q === (Std.triple (!! 2) (!! 1) (!! 2))), 1 answer {
    q=(2, 1, 2);
    }"];
  ()
;;

let%expect_test "" =
  let open Tester in
  let open Lib in
  let lesson group_id teacher_id course_id : Para.injected =
    OCanren.inj @@ Para.Lesson (group_id, teacher_id, course_id)
  in
  let constraint1 q =
    let _ : (Para.injected, Para.injected, Para.injected) Std.Triple.injected = q in
    q =/= Std.triple (lesson __ __ __) Para.blank (lesson __ __ __)
  in
  let run eta =
    run_r
      [%reify: (Para.ground, Para.ground, Para.ground) Std.Triple.t]
      ([%show: (Para.logic, Para.logic, Para.logic) Std.Triple.logic] ())
      eta
  in
  let filled_para = lesson !!1 !!"1" !!"1" in
  [%tester run 1 (fun q -> constraint1 q)];
  [%expect "
    fun q -> constraint1 q, 1 answer {
    q=_.10 [=/= (Lesson (_.-42, _.-42, _.-42), Window, Lesson (_.-42, _.-42, _.-42))];
    }"];
  (* Good case *)
  [%tester
    run 1 (fun q ->
      constraint1 q &&& (q === Std.triple Para.blank Para.blank filled_para))];
  [%expect "
    fun q ->
      (constraint1 q) &&& (q === (Std.triple Para.blank Para.blank filled_para)), 1 answer {
    q=(Window, Window, Lesson (1, \"1\", \"1\"));
    }"];
  (* Bad case *)
  [%tester
    run 1 (fun q ->
      constraint1 q &&& (q === Std.triple filled_para Para.blank filled_para))];
  [%expect "
    fun q ->
      (constraint1 q) &&& (q === (Std.triple filled_para Para.blank filled_para)), 1 answer {
    }"];
  ()
;;
