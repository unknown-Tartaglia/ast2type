function calculateStats(numbers) {
  if (!Array.isArray(numbers)) {
    return { average: 0, min: 0, max: 0, sum: 0 };
  }

  const validNumbers = numbers.filter(n => typeof n === 'number' && !isNaN(n));

  if (validNumbers.length === 0) {
    return { average: 0, min: 0, max: 0, sum: 0 };
  }

  const sum = validNumbers.reduce((acc, num) => acc + num, 0);
  const average = sum / validNumbers.length;
  const min = Math.min(...validNumbers);
  const max = Math.max(...validNumbers);

  return {
    average: Math.round(average * 100) / 100,
    min,
    max,
    sum
  };
}

module.exports = calculateStats;