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

let footer ppf () = fprintf ppf {|\end{document} %!|}

let pp_para kind pp_gid ppf =
  let open OCanren in
  function
  | OCanren.Var _ -> ()
  | OCanren.Value Para.Window -> fprintf ppf "---"
  | Value (Lesson (OCanren.Value gid, Value tid, Value lesid)) ->
    (match kind with
     | Teacher -> fprintf ppf {| \makecell{\small %a \\ %s}|} pp_gid gid lesid
     | Group -> fprintf ppf {|   \makecell{\small %s \\ %s}|} lesid tid)
  | _ -> assert false
;;

let out_shedule ?(kind = Teacher) pp_group_id pp_id id ppf (sh : Schedule.reifed) =
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
    List.iter (fun p -> fprintf ppf " & %a" (pp_para kind pp_group_id) p) line;
    printfn "\\\\";
    ()
  done;
  printfn {|\end{tabular}|};
  printfn {|\caption{%a}|} pp_id id;
  printfn {|\end{figure}|};
  printfn {|\end{frame}|};
  fprintf ppf "%!"
;;

let start_section ppf name = fprintf ppf "\\section{%s}\n\n" name
