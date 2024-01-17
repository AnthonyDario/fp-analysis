(* Uses CIL to parse the C AST *)
open GoblintCil

module E = Errormsg
module F = Frontc
module C = Cil

let parseOneFile fname = 
    let cabs, cil = F.parse_with_cabs fname () in
    Rmtmps.removeUnusedTemps cil ;
    cil ;;

let transform f = 
    List.iter (fun g -> 
        match g with
        | GType (_,_) -> 
            E.log "GType"
        | GCompTag (_,_) ->
            E.log "GCompTag"
        | GCompTagDecl (_,_) ->
            E.log "GCompTagDecl"
        | GEnumTag (_,_) ->
            E.log "GEnumTag"
        | GEnumTagDecl (_,_) ->
            E.log "GEnumTagDecl"
        | GVarDecl (_,_) ->
            E.log "GVarDecl"
        | GVar (_,_,_) ->
            E.log "GVar"
        | GFun (_,_) ->
            E.log "GFun"
        | GAsm (_,_) ->
            E.log "GAsm"
        | GPragma (_,_) ->
            E.log "GPragma"
        | GText _ ->
            E.log "GText"
        ) f.globals ;;

let parse () = 
    let f = (parseOneFile "c/test.c") in 
    transform f ;;
