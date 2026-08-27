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
            "background-color": "#e3e7e2",
            "border-color": "#9aa69f",
            "border-width": 1,
            color: "#17221c",
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
            "background-color": "#12634a",
            "border-color": "#084631",
            color: "#ffffff",
            "font-weight": 600,
            shape: "round-rectangle",
          },
        },
        {
          selector: 'node[category = "product"]',
          style: {
            "background-color": "#174d73",
            "border-color": "#103850",
            color: "#ffffff",
            shape: "round-rectangle",
          },
        },
        {
          selector: 'node[category = "tool"]',
          style: {
            "background-color": "#6b4a82",
            "border-color": "#4c315e",
            color: "#ffffff",
            shape: "round-rectangle",
          },
        },
        {
          selector: 'node[category = "tcb-direct"]',
          style: {
            "background-color": "#b9ddce",
            "border-color": "#12634a",
            "border-width": 2,
          },
        },
        {
          selector: 'node[category = "tcb-indirect"]',
          style: {
            "background-color": "#dcebe4",
            "border-color": "#659982",
          },
        },
        {
          selector: "edge",
          style: {
            "arrow-scale": 0.75,
            "curve-style": "bezier",
            "line-color": "#a7b1aa",
            "target-arrow-color": "#a7b1aa",
            "target-arrow-shape": "triangle",
            width: 1.2,
          },
        },
        { selector: "node.dimmed", style: { opacity: 0.14 } },
        {
          selector: "node.match",
          style: { "border-color": "#e28b25", "border-width": 4, opacity: 1 },
        },
        {
          selector: ":selected",
          style: {
            "border-color": "#e28b25",
            "border-width": 4,
            "line-color": "#e28b25",
            "target-arrow-color": "#e28b25",
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
      <button type="button" title="Zoom out" aria-label="Zoom out" onclick={() => zoom(0.8)}
        >−</button
      >
      <button type="button" title="Fit graph" onclick={fit}>Fit</button>
      <button type="button" title="Zoom in" aria-label="Zoom in" onclick={() => zoom(1.25)}
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
          type="button"
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
