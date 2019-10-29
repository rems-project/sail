#!/bin/sh
cat << END_HEADER
<!DOCTYPE html>
<title>TODO: CHANGE TITLE</title>
<link rel="stylesheet" href="prism.css">
<script src="prism.js"></script>
<script src="prism_sail.js"></script>
<p>TODO: include <a href="https://prismjs.com/download.html#themes=prism">prism.js</a></p>
<pre class=""><code class="language-sail line-numbers">
END_HEADER
cat
cat << END_FOOTER
</code>
</pre>
END_FOOTER
