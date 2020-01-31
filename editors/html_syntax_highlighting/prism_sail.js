Prism.languages.sail = {
      'comment': [
		{
			pattern: /(^|[^\\])\/\*[\s\S]*?(?:\*\/|$)/,
			lookbehind: true
		},
		{
			pattern: /(^|[^\\:])\/\/.*/,
			lookbehind: true,
			greedy: true
		}
	],
      // Depending on the implementation, strings may allow escaped newlines and quote-escape
      'string': {
	  pattern: /(["])(?:\1\1|\\(?:\r\n|[\s\S])|(?!\1)[^\\\r\n])*\1/,
	  greedy: true
      },
      'operator': /:|->|==|!=|{\||\|}|=>|=|\+|-|@|\(\)|\(|\)|_|;|&|~|\.\.|,|\^|\*/,
      'keyword': [
	  {
	      pattern: /(^|[^.])\b(type|union|register|function|clause|scattered|val|effect|end|true|false|let|if|then)\b/,
	      lookbehind: true
	  }
      ],
      //'builtin': /\b(?:fx|fy|xf[xy]?|yfx?)\b/,
      'builtin': /\b[A-Z][A-Za-z_\-\/0-9']*/,
      'variable': /\b'?[a-z_][A-Za-z_\-\/0-9']*/,
      //'function': /\b[a-z_]\w*(?:(?=\()|\/\d+)/,
      'number': /\b0b\d+|\b\d+\.?\d*/,
      // Custom operators are allowed
      'punctuation': /[(){}\[\],:]/
};

