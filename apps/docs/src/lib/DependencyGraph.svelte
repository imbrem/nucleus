<script lang="ts">
  import { base } from "$app/paths";
  import { onMount } from "svelte";
  import GraphView from "./GraphView.svelte";
  import {
    dependencyInventory,
    dependencyNodes,
    type DependencyInventoryEntry,
  } from "./dependency-presentation";
  import {
    crateNodes,
    loadRepositoryData,
    type RepositoryData,
  } from "./repository-data";
  import { graphCopy, statusMetrics } from "./site-content";

  let data: RepositoryData | undefined = $state();
  let inventory: DependencyInventoryEntry[] = $state([]);
  let error: string | undefined = $state();
  const format = new Intl.NumberFormat("en");

  onMount(() => {
    const controller = new AbortController();
    void loadRepositoryData(controller.signal)
      .then((loaded) => {
        data = loaded;
        inventory = dependencyInventory(loaded.dependencies);
      })
      .catch((cause: unknown) => {
        if (!controller.signal.aborted) {
          error =
            cause instanceof Error
              ? cause.message
              : "Could not load project status";
        }
      });
    return () => controller.abort();
  });
</script>

<section aria-labelledby="status-heading">
  <div class="section-heading">
    <div>
      <p class="eyebrow">Repository health</p>
      <h1 id="status-heading">Project status</h1>
    </div>
    <a class="api-link" href={`${base}/api/nucleus/`}
      >Rust API docs <span>→</span></a
    >
  </div>
  {#if error}
    <p class="error">{error}</p>
  {:else if data}
    <div class="metrics" aria-label="Project statistics">
      {#each statusMetrics as metric}
        <article class:tcb-metric={metric.emphasis ?? false}>
          <strong>{format.format(data.lines[metric.key])}</strong><span
            >{metric.label}</span
          >
        </article>
      {/each}
      <article>
        <strong>{data.crates.crates.length}</strong><span
          >production crates</span
        >
      </article>
      <article>
        <strong>{data.dependencies.packages.length}</strong><span
          >dependency versions</span
        >
      </article>
      <article>
        <strong>{inventory.length}</strong><span>dependency names</span>
      </article>
    </div>
  {:else}
    <p class="loading">Reading generated repository data…</p>
  {/if}
</section>

{#if data}
  <GraphView
    eyebrow={graphCopy.crates.eyebrow}
    title={graphCopy.crates.title}
    nodes={crateNodes(data.crates)}
    edges={data.crates.edges}
    compact
  />
  <a class="graph-page-link" href={`${base}/crates/`}>Open full crate graph →</a
  >

  <GraphView
    eyebrow={graphCopy.dependencies.eyebrow}
    title={graphCopy.dependencies.title}
    nodes={dependencyNodes(data.dependencies)}
    edges={data.dependencies.edges}
    compact
  />
  <a class="graph-page-link" href={`${base}/dependencies/`}
    >Open full dependency graph →</a
  >

  <section aria-labelledby="external-heading">
    <div class="section-heading">
      <div>
        <p class="eyebrow">Production dependency inventory</p>
        <h2 id="external-heading">External dependencies</h2>
      </div>
      <span class="dependency-total"
        >{data.dependencies.packages.length} versions</span
      >
    </div>
    <div class="dependency-inventory">
      {#each inventory as dependency}
        <div class="dependency-row">
          <span>{dependency.name}</span>
          <div>
            {#each dependency.versions as version}
              <code class={version.category} title={version.category}
                >{version.version}</code
              >
            {/each}
          </div>
        </div>
      {/each}
    </div>
  </section>
{/if}
