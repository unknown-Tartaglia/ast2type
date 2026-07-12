/*
 * @Date: 2021-12-30 14:25:53
 * @LastEditTime: 2022-04-06 20:08:21
 * @Description: file content
 */
import { EVENT_TYPE, PlatformUtils } from '@hw-vmall/vrn-basic-comp';
import { Dimensions } from 'react-native';

export default {
  clickItem(item: any, url) {
    const actionCode = actionCodefn();
    let indexDate = { index: null, indexName: null };
    if (item === 'ic5') {
      indexDate.indexName = '待付款';
      indexDate.index = '2';
    } else if (item === 'ic3') {
      indexDate.indexName = '待收货';
      indexDate.index = '3';
    } else if (item === 'ic4') {
      indexDate.indexName = '待评价';
      indexDate.index = '4';
    } else {
      indexDate = itemOther(indexDate, item);
    }
    const data = {
      actionCode: actionCode,
      actionName: '点击我的订单上报',
      eventType: EVENT_TYPE.EVENT_TYPE_CLICK,
      pageId: String(this.props.pageId),
      content: {
        comId: 'personalInfo_myOrder',
        gotoURL: url ? url : '',
        index: indexDate.index,
        indexName: indexDate.indexName,
      },
      pageCatCode: 'p_personalCenter',
      pageCatName: '个人中心',
      resSiteCode: 's_personalCenter_myorder',
      resSiteName: '我的订单',
    };
    return { data };
  },
};
function actionCodefn() {
  let actionCode = null;
  if (PlatformUtils.isApp()) {
    actionCode = '110000101';
  } else if (PlatformUtils.isPc(Dimensions.get('window').width)) {
    actionCode = '310000101';
  } else {
    actionCode = '210000101';
  }
  return actionCode;
}
function itemOther(indexDate: any, item: string) {
  if (item === 'ic1') {
    indexDate.indexName = '退换/退款';
    indexDate.index = '5';
  } else if (item === 'ic2') {
    indexDate.indexName = '回收单';
    indexDate.index = '6';
  } else if (item === 'all') {
    indexDate.indexName = '全部订单';
    indexDate.index = '1';
  } else if (item === 'ic_') {
    indexDate.indexName = '小程序';
    indexDate.index = '7';
  }
  return indexDate;
}
