<script lang="ts">
  import { onMount } from "svelte";
  import GraphView from "./GraphView.svelte";
  import {
    crateNodes,
    dependencyNodes,
    loadRepositoryData,
    type RepositoryData,
  } from "./repository-data";

  let { kind }: { kind: "crates" | "dependencies" } = $props();
  let data: RepositoryData | undefined = $state();
  let error: string | undefined = $state();

  onMount(() => {
    const controller = new AbortController();
    void loadRepositoryData(controller.signal)
      .then((loaded) => {
        data = loaded;
      })
      .catch((cause: unknown) => {
        if (!controller.signal.aborted) {
          error =
            cause instanceof Error
              ? cause.message
              : "Could not load repository data";
        }
      });
    return () => controller.abort();
  });
</script>

<main class="graph-page">
  {#if error}
    <p class="error">{error}</p>
  {:else if data && kind === "crates"}
    <GraphView
      eyebrow="Workspace topology"
      title="Crate graph"
      nodes={crateNodes(data.crates)}
      edges={data.crates.edges}
    />
  {:else if data}
    <GraphView
      eyebrow="Resolved by Cargo"
      title="Dependency graph"
      nodes={dependencyNodes(data.dependencies)}
      edges={data.dependencies.edges}
    />
  {:else}
    <p class="loading">Reading generated repository data…</p>
  {/if}
</main>
