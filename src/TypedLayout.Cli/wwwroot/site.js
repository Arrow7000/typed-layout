const source = document.querySelector("#source");
const analyzeButton = document.querySelector("#analyze");
const diagnostic = document.querySelector("#diagnostic");
const bindings = document.querySelector("#bindings");

source.value = `-- POC syntax: whitespace is insignificant and comments start with --
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
`;

async function analyze() {
  diagnostic.textContent = "Checking…";
  bindings.replaceChildren();

  try {
    const response = await fetch("/api/analyze", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ source: source.value })
    });
    const result = await response.json();

    if (!result.ok) {
      diagnostic.textContent = result.diagnostic;
      return;
    }

    diagnostic.textContent = "Layout checks for this target.";

    for (const binding of result.bindings) {
      const wrapper = document.createElement("div");
      wrapper.className = "binding";

      const name = document.createElement("button");
      name.type = "button";
      name.textContent = binding.name;
      name.title = binding.hoverText;
      name.addEventListener("click", () => {
        source.focus();
        source.setSelectionRange(binding.start, binding.end);
      });

      const type = document.createElement("pre");
      type.textContent = binding.hoverText;

      wrapper.append(name, type);
      bindings.append(wrapper);
    }
  } catch (error) {
    diagnostic.textContent = `Could not reach the compiler: ${error}`;
  }
}

analyzeButton.addEventListener("click", analyze);
source.addEventListener("keydown", event => {
  if ((event.ctrlKey || event.metaKey) && event.key === "Enter") analyze();
});

analyze();
