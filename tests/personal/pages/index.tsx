/*
 * @Date: 2021-03-03 14:22:50
 * @LastEditTime: 2022-04-06 20:10:01
 * @Description: 个人中心路由
 * @FilePath: \vrn-pages\src\pages\personal\index.tsx
 */
import { PlatformUtils, UrlUtils, CommonUtils } from '@hw-vmall/vrn-basic-comp';
import React, { Component } from 'react';
import { Dimensions } from 'react-native';
import PersonalRouter from '../router/personal';

let defaultRoute = 'PersonalDeault';
let params: { [prodName: string]: any } = {};
let screenWidth = 0;
let isWeb = function () {
  return PlatformUtils.isWeb();
};
if (isWeb()) {
  let categoryParams = UrlUtils.getQueryStr('PersonalParams') || '{}';
  params = JSON.parse(categoryParams);
  if (!CommonUtils.isEmpty(params) && params.targetRoute) {
    defaultRoute = params.targetRoute;
  } else {
    defaultRoute = 'PersonalDeault';
  }
  screenWidth = window.screen.width;
}
type CategoryPropsType = {
  categoryParams?: {
    targetRoute: string;
    targetParams?: {};
  };
  pageId?: string;
  DarkStyle?: boolean;
  pageAlias?: string;
};
class Personal extends Component<CategoryPropsType, any> {
  resizeListener: any;
  constructor(props) {
    super(props);
    if (PlatformUtils.isApp()) {
      let categoryParams = props?.categoryParams || '{}';
      params = JSON.parse(categoryParams);
      if (!CommonUtils.isEmpty(params) && params.targetRoute) {
        defaultRoute = params?.targetRoute;
      } else {
        defaultRoute = 'PersonalDeault';
      }
    }
  }
  componentDidMount() {
    if (isWeb() && PlatformUtils.isWap(Dimensions.get('window').width)) {
      this.resizeListener = window.addEventListener('resize', () => {
        if (Math.abs(window.screen.width - screenWidth) > 200) {
          window.location.reload();
        }
      });
    }
  }
  componentWillUnmount() {
    defaultRoute = 'PersonalDeault';
    if (isWeb()) {
      this.resizeListener && window.removeEventListener('resize', () => {});
    }
  }
  render() {
    return (
      <PersonalRouter
        defaultRoute={defaultRoute}
        personalParams={params}
        {...this.props}
      />
    );
  }
}

export default Personal;
