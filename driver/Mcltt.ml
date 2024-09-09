open Mcltt.Main

let () =
  if Array.length Sys.argv <> 2 then
    begin
      Printf.fprintf stderr "incorrect input: %s <input-file>\n" Sys.argv.(0);
      exit 1
    end;
  let filename = Sys.argv.(1) in
  main ~default_fp:filename ()
