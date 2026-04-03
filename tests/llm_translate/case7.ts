type FilterValue = any | any[] | ((value: any) => boolean);

interface Filters {
  [key: string]: FilterValue;
}

function searchItems(items: any[], filters: Filters): any[] {
  if (!Array.isArray(items) || !filters || typeof filters !== 'object') {
    return [];
  }

  return items.filter(item => {
    if (!item || typeof item !== 'object') {
      return false;
    }

    for (const key in filters) {
      if (filters[key] !== undefined) {
        if (item[key] === undefined) {
          return false;
        }

        if (typeof filters[key] === 'function') {
          if (!(filters[key] as Function)(item[key])) {
            return false;
          }
        } else if (Array.isArray(filters[key])) {
          if (!(filters[key] as any[]).includes(item[key])) {
            return false;
          }
        } else if (filters[key] !== item[key]) {
          return false;
        }
      }
    }

    return true;
  });
}

module.exports = searchItems;