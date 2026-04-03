import { handleIndexName } from '../../../../personal/utils/util';

export default {
  clickItem(actionCode, url, index, name, isVpro) {
    const data = {
      actionCode: actionCode?.toString(),
      actionName: '点击个人信息上报',
      pageId: this.props?.pageId?.toString(),
      eventType: '2',
      content: {
        comId: 'personalInfo',
        gotoURL: url || '',
        index: index.toString(),
        indexName: handleIndexName(Number(index)),
        isVIP: isVpro,
      },
      pageCatCode: 'p_personalCenter',
      pageCatName: '个人中心',
      resSiteCode: 's_personalCenter_asset',
      resSiteName: '用户资产',
    };
    return { data };
  },
};
