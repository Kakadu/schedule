//$ ./appendo.exe
//fun q -> fun r -> appendo q r (list (!!) [1; 2; 3; 4]), all answers {
//q=[]; r=[1; 2; 3; 4];
//q=[1]; r=[2; 3; 4];
//q=[1; 2]; r=[3; 4];
//q=[1; 2; 3]; r=[4];
//q=[1; 2; 3; 4]; r=[];
//}
//$ ./main.exe
//fun q -> substo (v varX) varX (v varY) q, 1 answer {
//q=V ("y");
//}
//fun q -> evalo (abs varX (v varX)) q, 1 answer {
//q=Abs ("x", V ("x"));
//}
//fun q -> evalo (abs varX (v varX)) q, 2 answers {
//q=Abs ("x", V ("x"));
//}
//fun q -> evalo (app (abs varX (v varX)) (v varY)) q, 1 answer {
//q=V ("y");
//}
//fun q -> evalo (app (abs varX (v varX)) q) (v varY), 1 answer {
//q=V ("y");
//}
//fun q -> evalo (app (abs varX q) (v varY)) (v varY), 1 answer {
//q=V ("x");
//}
//fun q -> evalo (app (v varX) (v varX)) q, 1 answer {
//q=App (V ("x"), V ("x"));
//}
//fun q -> evalo (v varX) q, 1 answer {
//q=V ("x");
//}
//fun q -> evalo (app q (v varX)) (v varX), 1 answer {
//q=Abs (_.44, V (_.44));
//}
//fun q -> fun r -> evalo (app r q) (v varX), 1 answer {
//q=V ("x"); r=Abs (_.54, V (_.54));
//}
//fun q -> fun r -> fun s -> a_la_quine q r s, 2 answers {
//q=Abs (_.668, V (_.668)); r=Abs (_.668, V (_.668)); s=Abs (_.668, V (_.668));
//q=Abs (_.783, V (_.783)); r=Abs (_.783, Abs (_.783, V (_.783))); s=Abs (_.783, Abs (_.783, V (_.783)));
//}



  $ ./for_ocaml_test.exe
  fun q -> fun r -> appendo q r (list (!!) [1; 2; 3; 4]), all answers {
  q=[]; r=[1; 2; 3; 4];
  q=[1]; r=[2; 3; 4];
  q=[1; 2]; r=[3; 4];
  q=[1; 2; 3]; r=[4];
  q=[1; 2; 3; 4]; r=[];
  }
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  2021pi-1 2021pi-2 zagl1 zagl2 Sartasov Rpo
  0: [("2021pi-1", [[_.6868; "teorver1"; "Rpo"; "diff1"]; [_.11307; "matlog1"; _.11308; _.11309]; [_.7195; _.7196; _.7197; _.7198]; [_.7373; _.7374; _.7375; _.7376]; [_.7513; _.7514; _.7515; _.7516]]); ("2021pi-2", [[_.14067; "diff2"; "Rpo"; "teorver2"]; [_.21664; _.21665; _.21666; "matlog2"]; [_.14770; _.14771; _.14772; _.14773]; [_.15106; _.15107; _.15108; _.15109]; [_.15437; _.15438; _.15439; _.15440]]); ("zagl1", [[_.793; _.794; "Rpo"; _.795]; [_.559; _.560; _.561; _.562]; [_.563; _.564; _.565; _.566]; [_.567; _.568; _.569; _.570]; [_.571; _.572; _.573; _.574]]); ("zagl2", [[_.796; _.797; "Rpo"; _.798]; [_.584; _.585; _.586; _.587]; [_.588; _.589; _.590; _.591]; [_.592; _.593; _.594; _.595]; [_.596; _.597; _.598; _.599]]); ("Sartasov", [[_.784; _.785; "Rpo"; _.786]; [_.484; _.485; _.486; _.487]; [_.488; _.489; _.490; _.491]; [_.492; _.493; _.494; _.495]; [_.496; _.497; _.498; _.499]]); ("Solev", [[_.1783; "teorver1"; _.1785; "teorver2"]; [_.1255; _.1256; _.1257; _.1258]; [_.1268; _.1269; _.1270; _.1271]; [_.1292; _.1293; _.1294; _.1295]; [_.1318; _.1319; _.1320; _.1321]]); ("Basov", [[_.5452; "diff2"; _.5453; "diff1"]; [_.3426; _.3427; _.3428; _.3429]; [_.3498; _.3499; _.3500; _.3501]; [_.3603; _.3604; _.3605; _.3606]; [_.3690; _.3691; _.3692; _.3693]]); ("Starchak", [[_.12008; _.12009; _.12010; _.12011]; [_.21667; "matlog1"; _.21669; "matlog2"]; [_.12687; _.12688; _.12689; _.12690]; [_.13095; _.13096; _.13097; _.13098]; [_.13446; _.13447; _.13448; _.13449]]); ("2020pi-2", [[_.48666; "Graph_theory1"; _.48667; _.48668]; [_.27845; _.27846; _.27847; _.27848]; [_.28519; _.28520; _.28521; _.28522]; [_.29176; _.29177; _.29178; _.29179]; [_.29881; _.29882; _.29883; _.29884]]); ("Grigoriev", [[_.48669; "Graph_theory1"; _.48670; _.48671]; [_.23753; _.23754; _.23755; _.23756]; [_.24443; _.24444; _.24445; _.24446]; [_.25083; _.25084; _.25085; _.25086]; [_.25673; _.25674; _.25675; _.25676]])]
  fun q -> fun r -> appendo q r (list (!!) [1; 2; 3; 4]), all answers {
  q=[]; r=[1; 2; 3; 4];
  q=[1]; r=[2; 3; 4];
  q=[1; 2]; r=[3; 4];
  q=[1; 2; 3]; r=[4];
  q=[1; 2; 3; 4]; r=[];
  }
