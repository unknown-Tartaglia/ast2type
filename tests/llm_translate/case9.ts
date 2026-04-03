interface PaginatedResult<T> {
  data: T[];
  page: number;
  pageSize: number;
  total: number;
  totalPages: number;
}

function paginate<T>(
  items: T[],
  page?: number,
  pageSize?: number,
  sortBy?: string | ((a: T, b: T) => number)
): PaginatedResult<T> {
  if (!Array.isArray(items)) {
    return { data: [], page: page || 1, pageSize: pageSize || 10, total: 0, totalPages: 0 };
  }

  let sortedItems = [...items];

  if (sortBy) {
    if (typeof sortBy === 'function') {
      sortedItems.sort(sortBy);
    } else if (typeof sortBy === 'string') {
      sortedItems.sort((a: any, b: any) => {
        const aVal = a[sortBy];
        const bVal = b[sortBy];
        if (aVal < bVal) return -1;
        if (aVal > bVal) return 1;
        return 0;
      });
    }
  }

  const total = sortedItems.length;
  let pageSizeNum: number;
  if (pageSize === undefined) {
    pageSizeNum = 10;
  } else if (pageSize === 0) {
    pageSizeNum = total > 0 ? total : 1;
  } else {
    pageSizeNum = Math.max(1, pageSize);
  }
  const totalPages = total === 0 ? 0 : Math.ceil(total / pageSizeNum);
  const currentPage = Math.max(1, Math.min(page || 1, totalPages || 1));
  const startIndex = (currentPage - 1) * pageSizeNum;
  const endIndex = Math.min(startIndex + pageSizeNum, total);

  const data = sortedItems.slice(startIndex, endIndex);

  return {
    data,
    page: currentPage,
    pageSize: pageSizeNum,
    total,
    totalPages
  };
}

module.exports = paginate;