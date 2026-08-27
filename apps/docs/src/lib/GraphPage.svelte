<script lang="ts">
  import { onMount } from "svelte";
  import { dependencyNodes } from "./dependency-presentation";
  import GraphView from "./GraphView.svelte";
  import {
    crateNodes,
    loadRepositoryData,
    type RepositoryData,
  } from "./repository-data";
  import { graphCopy } from "./site-content";

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
      eyebrow={graphCopy.crates.eyebrow}
      title={graphCopy.crates.title}
      nodes={crateNodes(data.crates)}
      edges={data.crates.edges}
    />
  {:else if data}
    <GraphView
      eyebrow={graphCopy.dependencies.eyebrow}
      title={graphCopy.dependencies.title}
      nodes={dependencyNodes(data.dependencies)}
      edges={data.dependencies.edges}
    />
  {:else}
    <p class="loading">Reading generated repository data…</p>
  {/if}
</main>
