let main () =
  if choice () then
    let elt = mousemove () in
    magnify elt;
    ()
  else
    let elt = mouseout () in
    minify elt;
    ()
