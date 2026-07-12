export default {
  clickItem(actionName, actionCode, url, index, name) {
    const data = {
      actionCode: actionCode?.toString(),
      actionName: '点击个人资产上报',
      pageId: this.props?.pageId?.toString(),
      eventType: '2',
      content: {
        comId: 'personalInfo_asset',
        gotoURL: url,
        index: index.toString(),
        indexName: name,
      },
      pageCatCode: 'p_personalCenter',
      pageCatName: '个人中心',
      resSiteCode: 's_personalCenter_asset',
      resSiteName: '用户资产'
    };
    return { data };
  },
};
