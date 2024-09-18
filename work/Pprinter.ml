open Lib
open Format

type kind =
  | Teacher
  | Group

let header ppf () =
  fprintf
    ppf
    {|
\documentclass[aspectratio=169]{beamer}
\setbeamertemplate{headline}{}
\setbeamertemplate{navigation symbols}{}
\usetheme{CambridgeUS}
\usepackage[quiet]{fontspec}
\usepackage{polyglossia}
\setmainlanguage{russian}
\setmainfont[Ligatures=TeX]{CMU Serif}
\setsansfont[Ligatures=TeX]{CMU Sans Serif}
\usepackage{makecell}

\begin{document}%!
|}
;;

let start_section ppf name = fprintf ppf "\\section{%s}\n\n" name
let footer ppf () = fprintf ppf {|\end{document} %!|}

let pp_para_teacher pp_gid ppf =
  let open OCanren in
  function
  | OCanren.Var _ ->
    (* print_endline ([%show: Para.logic] () v); *)
    ()
  | OCanren.Value Para.Window -> fprintf ppf "---"
  | Value (Lesson (OCanren.Value gid, Value tid, Value lesid)) ->
    fprintf ppf {| \makecell{\small %a \\ %s}|} pp_gid gid lesid
  | _ -> assert false
;;

let pp_para_group pp_gid ppf : Stud_para.logic -> _ =
  let open OCanren in
  let project_electives =
    let rec helper acc = function
      | Value OCanren.Std.List.Nil -> acc
      | Var _ -> failwith "Bad argument"
      | Value (Cons (Value (Value l, Value r), rest)) -> helper ((l, r) :: acc) rest
      | _ -> assert false
    in
    helper []
  in
  function
  | OCanren.Var _ ->
    (* print_endline ([%show: Para.logic] () v); *)
    ()
  | Value (Stud_para.Default (Value Para.Window)) -> fprintf ppf "---"
  | Value (Stud_para.Default (Value x)) ->
    (match x with
     | Lesson (OCanren.Value _, Value tid, Value lesid) ->
       fprintf ppf {|   \makecell{\small %s \\ %s}|} lesid tid
     | _ -> assert false)
  | Value (Stud_para.Elective (Value elename, lessons)) ->
    let electives = project_electives lessons in
    fprintf
      ppf
      {|   \makecell{\linespread{0.5}\tiny %s %s }|}
      elename
      (String.concat
         ""
         (List.map (fun (a, b) -> sprintf {|\\[-0.2cm]\tiny %s %s|} a b) electives))
  | _ -> assert false
;;

let out_shedule pp_group_id pp_id id pp_para ppf (sh : _ Schedule.reifed) =
  let printfn fmt = kasprintf (fprintf ppf "%s\n") fmt in
  printfn "\n";
  printfn {|\begin{frame}|};
  printfn {|\begin{figure}|};
  printfn {|\def\arraystretch{2}|};
  printfn {|\begin{tabular}{ c||c|c|c|c|c|c }|};
  printfn {|   & пн & вт & ср & чт & пт & су \\\hline|};
  for i = 1 to 4 do
    let line = List.map (fun xs -> List.nth xs (i - 1)) sh in
    fprintf ppf "%d " i;
    List.iter (fun p -> fprintf ppf " & %a" (pp_para pp_group_id) p) line;
    printfn "\\\\";
    ()
  done;
  printfn {|\end{tabular}|};
  printfn {|\caption{%a}|} pp_id id;
  printfn {|\end{figure}|};
  printfn {|\end{frame}|};
  fprintf ppf "%!"
;;

let out_teachers_schedule pp_group_id pp_id id ppf shed =
  let _ : Para.logic Schedule.reifed = shed in
  out_shedule pp_group_id pp_id id pp_para_teacher ppf shed
;;

let out_student_schedule pp_group_id pp_id id ppf shed =
  let _ : Stud_para.logic Schedule.reifed = shed in
  out_shedule pp_group_id pp_id id pp_para_group ppf shed
;;
