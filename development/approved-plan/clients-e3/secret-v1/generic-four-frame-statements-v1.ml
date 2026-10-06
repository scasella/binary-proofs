let bp_public_four_frame_preservation_statement =
 `!c:(S,V)component cs1:((S,A)component)list
    cs2:((S,B)component)list cs3:((S,C)component)list
    cs4:((S,D)component)list s t.
    ALL (orthogonal_components c) cs1 /\
    ALL (orthogonal_components c) cs2 /\
    ALL (orthogonal_components c) cs3 /\
    ALL (orthogonal_components c) cs4 /\
    (MAYCHANGE cs1 ,, MAYCHANGE cs2 ,,
     MAYCHANGE cs3 ,, MAYCHANGE cs4) s t
    ==> read c t = read c s`;;
