function analyzeText(text) {
  if (typeof text !== 'string') {
    return { wordCount: 0, charCount: 0, longestWord: '', averageLength: 0 };
  }

  const words = text.trim().split(/\s+/).filter(w => w.length > 0);
  const wordCount = words.length;
  const charCount = text.length;

  let longestWord = '';
  let totalWordLength = 0;

  words.forEach(word => {
    totalWordLength += word.length;
    if (word.length > longestWord.length) {
      longestWord = word;
    }
  });

  const averageLength = wordCount > 0 ? totalWordLength / wordCount : 0;

  return {
    wordCount,
    charCount,
    longestWord,
    averageLength: Math.round(averageLength * 100) / 100
  };
}

module.exports = analyzeText;