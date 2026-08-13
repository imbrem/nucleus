<script lang="ts">
  import cytoscape, { type Core, type ElementDefinition } from "cytoscape";
  import { onMount } from "svelte";
  import type { GraphEdge, GraphNode } from "./repository-data";

  interface Props {
    eyebrow: string;
    title: string;
    nodes: GraphNode[];
    edges: GraphEdge[];
    compact?: boolean;
  }

  let { eyebrow, title, nodes, edges, compact = false }: Props = $props();
  let container: HTMLDivElement;
  let graph: Core | undefined;
  let query = $state("");
  let selected: GraphNode | undefined = $state();

  function fit() {
    graph?.fit(graph.elements(), compact ? 24 : 36);
  }

  function zoom(factor: number) {
    if (!graph) return;
    graph.zoom({
      level: graph.zoom() * factor,
      renderedPosition: { x: graph.width() / 2, y: graph.height() / 2 },
    });
  }

  function search() {
    if (!graph) return;
    const term = query.trim().toLocaleLowerCase();
    graph.nodes().removeClass("match dimmed");
    if (!term) return;
    graph.nodes().addClass("dimmed");
    const matches = graph
      .nodes()
      .filter((node) =>
        String(node.data("name")).toLocaleLowerCase().includes(term),
      );
    matches.removeClass("dimmed").addClass("match");
    if (matches.length > 0) graph.fit(matches, 80);
  }

  onMount(() => {
    const ids = new Set(nodes.map((node) => node.id));
    const elements: ElementDefinition[] = [
      ...nodes.map((node) => ({
        data: {
          ...node,
          label: node.workspace ? node.name : `${node.name}\n${node.version}`,
        },
      })),
      ...edges
        .filter((edge) => ids.has(edge.source) && ids.has(edge.target))
        .map((edge, index) => ({
          data: {
            id: `edge-${index}`,
            source: edge.source,
            target: edge.target,
            kinds: edge.kinds.join(", "),
          },
        })),
    ];
    graph = cytoscape({
      container,
      elements,
      layout: {
        name: "breadthfirst",
        directed: true,
        padding: compact ? 24 : 36,
        spacingFactor: compact ? 1.1 : 1.35,
      },
      minZoom: 0.2,
      maxZoom: 3,
      wheelSensitivity: 0.18,
      style: [
        {
          selector: "node",
          style: {
            "background-color": "#252c3a",
            "border-color": "#526078",
            "border-width": 1,
            color: "#c8d3e0",
            height: 44,
            label: "data(label)",
            "font-family": 'ui-monospace, "Cascadia Code", monospace',
            "font-size": 11,
            "min-zoomed-font-size": "7px",
            "text-max-width": "150px",
            "text-valign": "center",
            "text-wrap": "wrap",
            width: 166,
          },
        },
        {
          selector: 'node[category = "tcb"]',
          style: {
            "background-color": "#476b34",
            "border-color": "#9ece6a",
            color: "#f2f8ed",
            "font-weight": 600,
            shape: "round-rectangle",
          },
        },
        {
          selector: 'node[category = "product"]',
          style: {
            "background-color": "#36558a",
            "border-color": "#7aa2f7",
            color: "#f3f6ff",
            shape: "round-rectangle",
          },
        },
        {
          selector: 'node[category = "tool"]',
          style: {
            "background-color": "#60477f",
            "border-color": "#bb9af7",
            color: "#fbf8ff",
            shape: "round-rectangle",
          },
        },
        {
          selector: 'node[category = "tcb-direct"]',
          style: {
            "background-color": "#314329",
            "border-color": "#9ece6a",
            "border-width": 2,
          },
        },
        {
          selector: 'node[category = "tcb-indirect"]',
          style: {
            "background-color": "#212d20",
            "border-color": "#789861",
          },
        },
        {
          selector: "edge",
          style: {
            "arrow-scale": 0.75,
            "curve-style": "bezier",
            "line-color": "#526078",
            "target-arrow-color": "#526078",
            "target-arrow-shape": "triangle",
            width: 1.2,
          },
        },
        { selector: "node.dimmed", style: { opacity: 0.14 } },
        {
          selector: "node.match",
          style: { "border-color": "#7aa2f7", "border-width": 4, opacity: 1 },
        },
        {
          selector: ":selected",
          style: {
            "border-color": "#7aa2f7",
            "border-width": 4,
            "line-color": "#7aa2f7",
            "target-arrow-color": "#7aa2f7",
          },
        },
      ],
    });
    graph.on("tap", "node", (event) => {
      selected = event.target.data() as GraphNode;
    });
    graph.on("tap", (event) => {
      if (event.target === graph) selected = undefined;
    });
    fit();
    return () => graph?.destroy();
  });
</script>

<section class:graph-preview={compact} aria-label={title}>
  <div class="section-heading graph-title">
    <div>
      <p class="eyebrow">{eyebrow}</p>
      <h2>{title}</h2>
    </div>
  </div>
  <div class="graph-toolbar graph-toolbar-simple">
    <label>
      <span class="sr-only">Find a crate</span>
      <input
        type="search"
        placeholder="Find a crate"
        bind:value={query}
        oninput={search}
      />
    </label>
    <div class="view-controls" aria-label="Graph view controls">
      <button title="Zoom out" aria-label="Zoom out" onclick={() => zoom(0.8)}
        >−</button
      >
      <button title="Fit graph" onclick={fit}>Fit</button>
      <button title="Zoom in" aria-label="Zoom in" onclick={() => zoom(1.25)}
        >+</button
      >
    </div>
  </div>
  <div class="graph-shell">
    <div
      class="graph"
      class:compact
      bind:this={container}
      aria-label={`Interactive ${title}`}
    ></div>
    {#if selected}
      <aside class="node-detail" aria-live="polite">
        <button
          aria-label="Close crate details"
          onclick={() => (selected = undefined)}>×</button
        >
        <span>{selected.category}</span><strong>{selected.name}</strong><code
          >{selected.version}</code
        >
      </aside>
    {/if}
  </div>
</section>
