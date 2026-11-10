let onblur () store_passwd =
  fun () -> ()

(* reachabilty query: when can I successfully recover a password.
   a 
*)

let client () =
  let recover_password passwd = _ in
  let domain = getDomain () in
  if hasPassword domain then
    recover_password (getPassword domain);
  
  onblur p store_passwd;
  
