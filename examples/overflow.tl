-- This program fails: two non-shrinking 100px flex items need 200px.
viewport 500px 600px

child =
    div
        [ display block
        , width 100px
        , height 40px
        , flex-shrink 0
        ]
        []

main =
    div
        [ display flex
        , width 180px
        ]
        [ child, child ]
