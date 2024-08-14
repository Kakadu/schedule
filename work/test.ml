open Lib

include struct
  open OCanren

  type 'a assoc_schedule =
    ('a ilogic, Schedule.injected) Std.Pair.injected Std.List.injected

  type injected_answer = (int assoc_schedule, string assoc_schedule) Std.Pair.injected

  type main_reifier = (injected_answer, 'g * 't) Reifier.t
    constraint 'g = (int * Schedule.reifed) Std.List.ground
    constraint 't = (GT.string * Schedule.reifed) Std.List.ground

  let reify_delogic_sheds : main_reifier =
    Std.Pair.prj_exn
      (Std.List.prj_exn (Std.Pair.prj_exn prj_exn Schedule.reify))
      (Std.List.prj_exn (Std.Pair.prj_exn prj_exn Schedule.reify))
  ;;

  let inject_into_single ~group_shedules ~teacher_shedules (sheds : injected_answer) =
    let wrap ht =
      Hashtbl.to_seq ht |> Stdlib.List.of_seq |> Std.list (fun (a, b) -> Std.pair !!a b)
    in
    let teacher_as_list = wrap teacher_shedules in
    let groups_as_list = wrap group_shedules in
    sheds === Std.pair groups_as_list teacher_as_list
  ;;
end

module Int_set = Set.Make (Int)

let run teachers plan : _ =
  let _ : Plan.pre_plan = plan in
  let all_groups =
    List.fold_left
      (fun acc { Plan_item.group_id; _ } -> Int_set.add group_id acc)
      Int_set.empty
      plan
  in
  let group_shedules : (group_id, Schedule.injected) Hashtbl.t =
    Hashtbl.create (Int_set.cardinal all_groups)
  in
  let init_group_sheds =
    Int_set.fold
      (fun gid acc ->
        let open OCanren in
        Fresh.one (fun shed ->
          Hashtbl.add group_shedules gid shed;
          (* log "Group shedules count = %d" (Hashtbl.length group_shedules); *)
          (* log "all_groups count = %d" (Int_set.cardinal all_groups); *)
          acc &&& Lib.init_empty_schedule shed))
      all_groups
      OCanren.success
  in
  let teacher_shedules : (string, Schedule.injected) Hashtbl.t =
    Hashtbl.create (List.length teachers)
  in
  let init_teacher_sheds =
    List.fold_left
      (fun acc teacher ->
        let open OCanren in
        Fresh.one (fun shed ->
          Hashtbl.add teacher_shedules teacher.Teacher.id shed;
          (* log "add to teachers shedule with key = %s" teacher.Teacher.id; *)
          acc &&&& Teacher.init_schedule teacher shed))
      OCanren.success
      teachers
  in
  let get_teacher tid = List.find (fun { Teacher.id; _ } -> tid = id) teachers in
  let get_teacher_sched tid =
    (* log "Teacher shedules count = %d" (Hashtbl.length teacher_shedules); *)
    (* log "Teachers count = %d" (List.length teachers); *)
    try Hashtbl.find teacher_shedules tid with
    | Not_found -> Format.kasprintf failwith "Can't get schedule for teacher %s" tid
  in
  let get_group_sched tid = Hashtbl.find group_shedules tid in
  let plan = Plan.of_pre_plan plan in
  OCanren.(run one)
    (fun sheds ->
      let open OCanren in
      init_teacher_sheds
      &&&& init_group_sheds
      &&&& debug_var !!1 OCanren.reify (fun _ ->
        inject_into_single ~group_shedules ~teacher_shedules sheds)
      &&&& delay (fun () ->
        Lib.synth get_teacher ~get_teacher_sched ~get_group_sched plan))
    (fun (shed : _ OCanren.reified) : _ -> shed#reify reify_delogic_sheds)
;;

type config = { mutable out_tex_file : string }

let cfg = { out_tex_file = "" }

let test1 () =
  Plan.clear ();
  let teachers =
    [ Teacher.create "Kakadu" [ Bad_day 3; Bad_lesson 0 ]
    ; Teacher.create "Соловьёв" []
    ; Teacher.create "Виденский" []
    ; Teacher.create "Невзоров" []
    ; Teacher.create "ТеорВ-практик" []
    ; Teacher.create "Рябов" []
    ; Teacher.create "Евдокимова" []
    ; Teacher.create "Хит" []
    ]
  in
  let plan : Plan.pre_plan =
    [ Plan.make ~g:"ПИ2" ~t:"Kakadu" "ФП"
    ; Plan.make ~g:"ПИ3" ~t:"Kakadu" "Трансляции 1"
    ; Plan.make ~g:"ПИ3" ~t:"Kakadu" "Трансляции 2"
    ; Plan.make ~g:"ТП4" ~t:"Kakadu" "Трансляции"
    ; Plan.make ~cstrnts:[ Hardcode (1, 1) ] ~g:"ТП4" ~t:"Соловьёв" "ТВПиС"
    ; Plan.make ~cstrnts:[ Dont_ovelap "ТП3" ] ~g:"ТП4" ~t:"Kakadu" "ФП"
    ; Plan.make ~g:"ТП3" ~t:"Kakadu" "ФП"
    ; Plan.make ~g:"ТП3" ~t:"Виденский" "ФункАн 1"
    ; Plan.make ~g:"ТП3" ~t:"Виденский" "ФункАн 2"
    ; Plan.make ~g:"ТП3" ~t:"Невзоров" "Теорвер Л"
    ; Plan.make ~g:"ТП3" ~t:"ТеорВ-практик" "Теорвер П"
    ; Plan.make ~g:"ТП3" ~t:"Рябов" "ВыЧи (л)"
    ; Plan.make ~g:"ТП3" ~t:"Евдокимова" "ВыЧи (п)"
    ; Plan.make ~g:"ТП3" ~t:"Хит" "ТФЯТ 1"
    ; Plan.make ~g:"ТП3" ~t:"Хит" "ТФЯТ 2"
    ]
  in
  let g_sched, teachers_sched = run teachers plan |> OCanren.Stream.hd in
  let g_sched =
    List.sort
      (fun (a, _) (b, _) -> String.compare (Plan.group_of_id a) (Plan.group_of_id b))
      g_sched
  in
  let teachers_sched =
    List.sort (fun (a, _) (b, _) -> String.compare a b) teachers_sched
  in
  if cfg.out_tex_file <> ""
  then
    Out_channel.with_open_text cfg.out_tex_file (fun ch ->
      let pp_gid ppf gid = Format.pp_print_string ppf (Plan.group_of_id gid) in
      let ppf = Format.formatter_of_out_channel ch in
      Pprinter.header ppf ();
      Pprinter.start_section ppf "Преподы";
      List.iter
        (fun (tid, sched) ->
          Pprinter.out_shedule pp_gid Format.pp_print_string tid ppf sched)
        teachers_sched;
      Pprinter.start_section ppf "Студенческие группы";
      List.iter
        (fun (tid, sched) ->
          Pprinter.(out_shedule ~kind:Group)
            pp_gid
            Format.pp_print_string
            (Plan.group_of_id tid)
            ppf
            sched)
        g_sched;
      Pprinter.footer ppf ();
      Out_channel.flush ch)
;;

let () =
  Arg.parse
    [ "-tex", Arg.String (fun s -> cfg.out_tex_file <- s), "out TEX file"
    ; "-test1", Arg.Unit test1, " help"
    ]
    (fun _ -> assert false)
    ""
;;
