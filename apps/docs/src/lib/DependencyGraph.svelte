<script lang="ts">
  import { base } from '$app/paths';
  import cytoscape, { type Core, type ElementDefinition, type NodeSingular } from 'cytoscape';
  import { onMount } from 'svelte';

  type Scope = 'internal' | 'direct' | 'all';

  interface CargoNode {
    id: string;
    name: string;
    version: string;
    workspace: boolean;
    direct: boolean;
    category: 'tcb' | 'product' | 'tool' | 'external';
  }

  interface CargoGraph {
    nodes: CargoNode[];
    edges: Array<{
      source: string;
      target: string;
      kinds: string[];
    }>;
  }

  interface LineCounts {
    total: number;
    crates: number;
    tcb: number;
  }

  let container: HTMLDivElement;
  let graph: Core | undefined;
  let error: string | undefined;
  let scope: Scope = 'direct';
  let tcbOnly = false;
  let query = '';
  let selected: CargoNode | undefined;
  let cargo: CargoGraph | undefined;
  let lines: LineCounts | undefined;

  const format = new Intl.NumberFormat('en');

  function visible(node: NodeSingular): boolean {
    const category = node.data('category') as CargoNode['category'];
    if (tcbOnly) return category === 'tcb';
    if (scope === 'internal') return category !== 'external';
    if (scope === 'direct') return category !== 'external' || node.data('direct') === true;
    return true;
  }

  function refresh(fit = true) {
    if (!graph) return;
    graph.batch(() => {
      graph?.nodes().forEach((node) => {
        node.toggleClass('filtered', !visible(node));
      });
      graph?.edges().forEach((edge) => {
        edge.toggleClass(
          'filtered',
          edge.source().hasClass('filtered') || edge.target().hasClass('filtered'),
        );
      });
    });
    search(false);
    if (fit) graph.fit(graph.elements(':visible'), 36);
  }

  function setScope(next: Scope) {
    scope = next;
    tcbOnly = false;
    selected = undefined;
    refresh();
  }

  function toggleTcb() {
    tcbOnly = !tcbOnly;
    selected = undefined;
    refresh();
  }

  function search(fit = true) {
    if (!graph) return;
    const term = query.trim().toLocaleLowerCase();
    graph.nodes().removeClass('match dimmed');
    if (!term) return;
    const shown = graph.nodes(':visible');
    shown.addClass('dimmed');
    const matches = shown.filter((node) =>
      String(node.data('name')).toLocaleLowerCase().includes(term),
    );
    matches.removeClass('dimmed').addClass('match');
    if (fit && matches.length > 0) graph.fit(matches, 80);
  }

  function zoom(factor: number) {
    if (!graph) return;
    graph.zoom({
      level: graph.zoom() * factor,
      renderedPosition: { x: graph.width() / 2, y: graph.height() / 2 },
    });
  }

  onMount(() => {
    const controller = new AbortController();

    async function render() {
      const [graphResponse, locResponse] = await Promise.all([
        fetch(`${base}/generated/cargo-graph.json`, { signal: controller.signal }),
        fetch(`${base}/generated/loc.json`, { signal: controller.signal }),
      ]);
      if (!graphResponse.ok || !locResponse.ok) {
        throw new Error(
          `Status request failed: graph ${graphResponse.status}, LoC ${locResponse.status}`,
        );
      }
      cargo = (await graphResponse.json()) as CargoGraph;
      lines = (await locResponse.json()) as LineCounts;
      const elements: ElementDefinition[] = [
        ...cargo.nodes.map((node) => ({
          data: {
            ...node,
            label: node.workspace ? node.name : `${node.name}\n${node.version}`,
          },
        })),
        ...cargo.edges.map((edge, index) => ({
          data: {
            id: `edge-${index}`,
            source: edge.source,
            target: edge.target,
            kinds: edge.kinds.join(', '),
          },
        })),
      ];

      graph = cytoscape({
        container,
        elements,
        layout: {
          name: 'breadthfirst',
          directed: true,
          padding: 36,
          spacingFactor: 1.35,
        },
        minZoom: 0.35,
        maxZoom: 3,
        wheelSensitivity: 0.18,
        style: [
          {
            selector: 'node',
            style: {
              'background-color': '#e3e7e2',
              'border-color': '#9aa69f',
              'border-width': 1,
              color: '#17221c',
              height: 44,
              label: 'data(label)',
              'font-family': 'ui-monospace, "Cascadia Code", monospace',
              'font-size': 11,
              'min-zoomed-font-size': '7px',
              'text-max-width': '150px',
              'text-valign': 'center',
              'text-wrap': 'wrap',
              width: 166,
            },
          },
          {
            selector: 'node[category = "tcb"]',
            style: {
              'background-color': '#12634a',
              'border-color': '#084631',
              color: '#ffffff',
              'font-weight': 600,
              height: 50,
              shape: 'round-rectangle',
              width: 178,
            },
          },
          {
            selector: 'node[category = "product"]',
            style: {
              'background-color': '#174d73',
              'border-color': '#103850',
              color: '#ffffff',
              shape: 'round-rectangle',
            },
          },
          {
            selector: 'node[category = "tool"]',
            style: {
              'background-color': '#6b4a82',
              'border-color': '#4c315e',
              color: '#ffffff',
              shape: 'round-rectangle',
            },
          },
          {
            selector: 'node[direct = true]',
            style: {
              'border-color': '#b96818',
              'border-width': 2,
            },
          },
          {
            selector: 'edge',
            style: {
              'arrow-scale': 0.75,
              'curve-style': 'bezier',
              'line-color': '#a7b1aa',
              'target-arrow-color': '#a7b1aa',
              'target-arrow-shape': 'triangle',
              width: 1.2,
            },
          },
          {
            selector: '.filtered',
            style: { display: 'none' },
          },
          {
            selector: 'node.dimmed',
            style: { opacity: 0.16 },
          },
          {
            selector: 'node.match',
            style: {
              'border-color': '#e28b25',
              'border-width': 4,
              opacity: 1,
            },
          },
          {
            selector: ':selected',
            style: {
              'border-color': '#e28b25',
              'border-width': 4,
              'line-color': '#e28b25',
              'target-arrow-color': '#e28b25',
            },
          },
        ],
      });
      graph.on('tap', 'node', (event) => {
        selected = cargo?.nodes.find((node) => node.id === event.target.id());
      });
      graph.on('tap', (event) => {
        if (event.target === graph) selected = undefined;
      });
      refresh();
    }

    void render().catch((cause: unknown) => {
      if (!controller.signal.aborted) {
        error = cause instanceof Error ? cause.message : 'Could not load project status';
      }
    });

    return () => {
      controller.abort();
      graph?.destroy();
      graph = undefined;
    };
  });
</script>

<section aria-labelledby="status-heading">
  <div class="section-heading">
    <div>
      <p class="eyebrow">Repository health</p>
      <h2 id="status-heading">Project status</h2>
    </div>
    <a class="api-link" href={`${base}/api/nucleus/`}>Rust API docs <span>→</span></a>
  </div>

  {#if error}
    <p class="error">{error}</p>
  {:else if cargo && lines}
    <div class="metrics" aria-label="Project statistics">
      <article>
        <strong>{format.format(lines.total)}</strong>
        <span>total LoC</span>
      </article>
      <article>
        <strong>{format.format(lines.crates)}</strong>
        <span>crates LoC</span>
      </article>
      <article class="tcb-metric">
        <strong>{format.format(lines.tcb)}</strong>
        <span>TCB LoC</span>
      </article>
      <article>
        <strong>{cargo.nodes.filter((node) => node.workspace).length}</strong>
        <span>internal crates</span>
      </article>
      <article>
        <strong>{cargo.nodes.filter((node) => node.direct).length}</strong>
        <span>direct dependencies</span>
      </article>
      <article>
        <strong>{cargo.nodes.filter((node) => !node.workspace && !node.direct).length}</strong>
        <span>indirect dependencies</span>
      </article>
    </div>
  {:else}
    <p class="loading">Reading generated repository data…</p>
  {/if}
</section>

<section aria-labelledby="dependency-heading">
  <div class="section-heading graph-title">
    <div>
      <p class="eyebrow">Resolved by Cargo</p>
      <h2 id="dependency-heading">Dependency graph</h2>
    </div>
    <button class:active={tcbOnly} class="tcb-toggle" type="button" onclick={toggleTcb}>
      {tcbOnly ? 'Show project graph' : 'TCB only'}
    </button>
  </div>

  <div class="graph-toolbar">
    <div class="scope" aria-label="Graph scope">
      <button class:active={!tcbOnly && scope === 'internal'} onclick={() => setScope('internal')}
        >Internal</button
      >
      <button class:active={!tcbOnly && scope === 'direct'} onclick={() => setScope('direct')}
        >+ direct</button
      >
      <button class:active={!tcbOnly && scope === 'all'} onclick={() => setScope('all')}
        >All</button
      >
    </div>
    <label>
      <span class="sr-only">Find a crate</span>
      <input
        type="search"
        placeholder="Find a crate"
        bind:value={query}
        oninput={() => search()}
      />
    </label>
    <div class="view-controls" aria-label="Graph view controls">
      <button title="Zoom out" aria-label="Zoom out" onclick={() => zoom(0.8)}>−</button>
      <button title="Fit graph" onclick={() => refresh()}>Fit</button>
      <button title="Zoom in" aria-label="Zoom in" onclick={() => zoom(1.25)}>+</button>
    </div>
  </div>

  <div class="legend" aria-label="Graph legend">
    <span><i class="tcb"></i> TCB</span>
    <span><i class="product"></i> product</span>
    <span><i class="tool"></i> tool</span>
    <span><i class="direct"></i> direct external</span>
    <span><i></i> indirect external</span>
  </div>

  <div class="graph-shell">
    <div
      class="graph"
      class:hidden={error}
      bind:this={container}
      aria-label="Interactive Cargo dependency graph"
    ></div>
    {#if selected}
      <aside class="node-detail" aria-live="polite">
        <button aria-label="Close crate details" onclick={() => (selected = undefined)}>×</button>
        <span>{selected.category === 'external' ? (selected.direct ? 'direct' : 'indirect') : selected.category}</span>
        <strong>{selected.name}</strong>
        <code>{selected.version}</code>
      </aside>
    {/if}
  </div>
  <p class="graph-help">Drag to pan, scroll or pinch to zoom, and select a crate for details.</p>
</section>

{#if cargo}
  <section aria-labelledby="external-heading">
    <div class="section-heading">
      <div>
        <p class="eyebrow">Auditable inventory</p>
        <h2 id="external-heading">External dependencies</h2>
      </div>
      <span class="dependency-total"
        >{cargo.nodes.filter((node) => !node.workspace).length} resolved</span
      >
    </div>
    <div class="dependency-columns">
      <div>
        <h3>Direct</h3>
        <ul>
          {#each cargo.nodes.filter((node) => node.direct) as node}
            <li><span>{node.name}</span><code>{node.version}</code></li>
          {/each}
        </ul>
      </div>
      <div>
        <h3>Indirect</h3>
        <ul>
          {#each cargo.nodes.filter((node) => !node.workspace && !node.direct) as node}
            <li><span>{node.name}</span><code>{node.version}</code></li>
          {/each}
        </ul>
      </div>
    </div>
  </section>
{/if}
