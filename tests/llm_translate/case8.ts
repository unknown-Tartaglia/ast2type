interface Values {
  [key: string]: any;
}

function formatString(template: string, values: Values): string {
  if (typeof template !== 'string') {
    return '';
  }

  if (!values || typeof values !== 'object') {
    return template;
  }

  return template.replace(/\{(\w+)\}/g, (match, key) => {
    return values[key] !== undefined ? String(values[key]) : match;
  });
}

module.exports = formatString;