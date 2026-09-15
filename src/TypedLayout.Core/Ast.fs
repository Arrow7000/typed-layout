namespace TypedLayout

type Element =
    { Name: string
      TagName: string
      Declarations: Declaration list
      Children: Element list }

[<RequireQualifiedAccess>]
module Element =
    let create name tagName declarations children =
        { Name = name
          TagName = tagName
          Declarations = declarations
          Children = children }

    let div name declarations children =
        create name "div" declarations children
