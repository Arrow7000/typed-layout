-- A first standalone Typed Layout program.
viewport 500px 600px

first =
    div
        [ display block
        , width 100px
        , height 40px
        , flex-shrink 0
        ]
        []

second =
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
        , width auto
        , gap 12px
        ]
        [ first, second ]
