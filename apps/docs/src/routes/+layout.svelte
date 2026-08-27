<script lang="ts">
  import { base } from "$app/paths";
  import { navigation } from "$lib/site-content";
  import "../app.css";

  let { children } = $props();
</script>

<nav class="site-nav" aria-label="Primary navigation">
  {#each navigation as item}
    <a href={`${base}${item.href}`}>{item.label}</a>
  {/each}
</nav>

{@render children()}
